import BstLean.Part268CellShard5Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12475_20 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (16676642377297 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570039125247 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨20, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (16676642377297 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570039125247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_21 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (20837164465283 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280160508937 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨21, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (20837164465283 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280160508937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_22 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (8331412817427 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456032901141 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨22, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (8331412817427 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456032901141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_23 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83279622792819 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280168495439 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨23, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83279622792819 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280168495439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_24 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83245141683867 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570043120513 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨24, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83245141683867 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570043120513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_25 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (5200667800917 / 6250000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280176527591 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨25, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (5200667800917 / 6250000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280176527591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_26 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (4158812607633 / 5000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140090259387 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨26, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (4158812607633 / 5000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140090259387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_27 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41570921832713 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (71255766161 / 3125000000000 : ℝ))
      (E := (cell12475 ⟨27, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41570921832713 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (71255766161 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_28 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83107459320729 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280188525697 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨28, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83107459320729 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280188525697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_29 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41536549543247 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (57004812217 / 2500000000000 : ℝ))
      (E := (cell12475 ⟨29, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41536549543247 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (57004812217 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_30 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (20759690732703 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570049131379 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨30, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (20759690732703 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570049131379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_31 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41502225410967 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570050130381 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨31, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41502225410967 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570050130381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_32 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (3318806509131 / 4000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280204478677 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨32, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (3318806509131 / 4000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280204478677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_33 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82935898618411 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456041703169 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨33, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82935898618411 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456041703169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_34 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82901658461079 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570053129379 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨34, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82901658461079 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570053129379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_35 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82867442225173 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280216484981 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨35, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82867442225173 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280216484981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_36 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (20708312469937 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456044095587 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨36, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (20708312469937 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456044095587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_37 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41399540697007 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280224497289 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨37, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41399540697007 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280224497289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_38 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82764936737339 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280228485049 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨38, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82764936737339 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280228485049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_39 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (16546163175849 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280232500309 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨39, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (16546163175849 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280232500309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12476_20 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (833832026999 / 1000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140012183191 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨20, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (833832026999 / 1000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140012183191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_21 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83348648994423 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (114001417091 / 5000000000000 : ℝ))
      (E := (cell12476 ⟨21, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83348648994423 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (114001417091 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_22 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83314119626991 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280032365101 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨22, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83314119626991 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280032365101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_23 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83279614564523 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142502270237 / 6250000000000 : ℝ))
      (E := (cell12476 ⟨23, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83279614564523 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142502270237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_24 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83245133774109 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280040338431 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨24, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83245133774109 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280040338431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_25 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (2600333663219 / 3125000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228004435439 / 10000000000000 : ℝ))
      (E := (cell12476 ⟨25, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (2600333663219 / 3125000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228004435439 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_26 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83176244878647 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280048316711 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨26, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83176244878647 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280048316711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_27 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83141836708621 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140026172683 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨27, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83141836708621 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140026172683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_28 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (8310745268069 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570014081627 / 25000000000000 : ℝ))
      (E := (cell12476 ⟨28, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (8310745268069 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570014081627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_29 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83073092762781 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280060321271 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨29, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83073092762781 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280060321271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_30 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16607751384597 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280064332159 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨30, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16607751384597 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280064332159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_31 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83004445129553 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140034151467 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨31, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83004445129553 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140034151467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_32 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82970157350903 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280072352643 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨32, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82970157350903 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280072352643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_33 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (8293589355561 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228007630749 / 10000000000000 : ℝ))
      (E := (cell12476 ⟨33, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (8293589355561 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228007630749 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_34 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82901653712413 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140040172337 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨34, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82901653712413 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140040172337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_35 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41433718895103 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280084348411 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨35, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41433718895103 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280084348411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_36 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16566649151609 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570022079941 / 25000000000000 : ℝ))
      (E := (cell12476 ⟨36, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16566649151609 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570022079941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_37 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82799077585141 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140046159113 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨37, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82799077585141 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140046159113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_38 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41382466620431 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140048172241 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨38, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41382466620431 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140048172241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_39 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (20682703173683 / 25000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280100340291 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨39, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (20682703173683 / 25000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280100340291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12477_20 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83383193515027 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279892227587 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨20, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83383193515027 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279892227587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_21 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83348640129387 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279896228833 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨21, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83348640129387 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279896228833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_22 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16662822216269 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227990022039 / 10000000000000 : ℝ))
      (E := (cell12477 ⟨22, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16662822216269 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227990022039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_23 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83279606337821 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279904206403 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨23, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83279606337821 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279904206403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_24 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41622562932953 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279908249133 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨24, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41622562932953 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279908249133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_25 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (4160533481643 / 5000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (91196489423 / 4000000000000 : ℝ))
      (E := (cell12477 ⟨25, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (4160533481643 / 5000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (91196489423 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_26 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (8317623760611 / 10000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139958113747 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨26, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (8317623760611 / 10000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139958113747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_27 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83141829753253 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569980057023 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨27, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83141829753253 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569980057023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_28 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (1662148920841 / 2000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139962120169 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨28, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (1662148920841 / 2000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139962120169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_29 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20768271610107 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279928208501 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨29, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20768271610107 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279928208501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_30 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41519375458239 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455986438701 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨30, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41519375458239 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455986438701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_31 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41502219719227 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (284992024703 / 12500000000000 : ℝ))
      (E := (cell12477 ⟨31, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41502219719227 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (284992024703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_32 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82970151974773 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279940222901 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨32, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82970151974773 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279940222901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_33 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82935888494013 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279944212589 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨33, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82935888494013 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279944212589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_34 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82901648964911 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227994822679 / 10000000000000 : ℝ))
      (E := (cell12477 ⟨34, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82901648964911 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227994822679 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_35 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16573486671273 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139976104127 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨35, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16573486671273 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139976104127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_36 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82833241637429 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569989054169 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨36, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82833241637429 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569989054169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_37 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20699768444329 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227996019431 / 10000000000000 : ℝ))
      (E := (cell12477 ⟨37, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20699768444329 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227996019431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_38 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16552985949079 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279964200447 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨38, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16552985949079 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279964200447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_39 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82730809511191 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139984117773 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨39, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82730809511191 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139984117773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12478_20 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83383184331867 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (113988007143 / 5000000000000 : ℝ))
      (E := (cell12478 ⟨20, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83383184331867 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (113988007143 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_21 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (10418578908253 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (113988208499 / 5000000000000 : ℝ))
      (E := (cell12478 ⟨21, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (10418578908253 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (113988208499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_22 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83314102537333 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279768188177 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨22, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83314102537333 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279768188177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_23 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41639799056357 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139886071637 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨23, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41639799056357 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139886071637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_24 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41622558979629 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (71243004869 / 3125000000000 : ℝ))
      (E := (cell12478 ⟨24, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41622558979629 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (71243004869 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_25 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83210662044227 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569945042787 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨25, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83210662044227 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569945042787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_26 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83176230335049 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279784134333 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨26, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83176230335049 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279784134333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_27 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41570911399661 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455957633067 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨27, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41570911399661 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455957633067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_28 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83107439404807 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455958430061 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨28, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83107439404807 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455958430061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_29 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83073080119433 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (18238369203 / 800000000000 : ℝ))
      (E := (cell12478 ⟨29, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83073080119433 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (18238369203 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_30 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (8303874491129 / 10000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (45596003361 / 2000000000000 : ℝ))
      (E := (cell12478 ⟨30, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (8303874491129 / 10000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (45596003361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_31 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (20751108437159 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455960829417 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨31, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (20751108437159 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455960829417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_32 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41485073299943 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284976018499 / 12500000000000 : ℝ))
      (E := (cell12478 ⟨32, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41485073299943 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284976018499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_33 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82935883433619 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455962434517 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨33, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82935883433619 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455962434517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_34 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41450822109287 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455963232773 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨34, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41450822109287 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455963232773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_35 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82867428923649 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (28497751539 / 1250000000000 : ℝ))
      (E := (cell12478 ⟨35, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82867428923649 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (28497751539 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_36 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (828332375179 / 1000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (91192966747 / 4000000000000 : ℝ))
      (E := (cell12478 ⟨36, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (828332375179 / 1000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (91192966747 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_37 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82799069970539 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279828125543 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨37, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82799069970539 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279828125543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_38 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41382463125469 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139916085151 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨38, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41382463125469 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139916085151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_39 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82730806328621 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139918063687 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨39, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82730806328621 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139918063687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12479_20 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83383175150419 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (284953521307 / 12500000000000 : ℝ))
      (E := (cell12479 ⟨20, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83383175150419 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (284953521307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_21 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41674311202167 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279632165257 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨21, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41674311202167 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279632165257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_22 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41657046997477 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279636151857 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨22, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41657046997477 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279636151857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_23 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (208198974723 / 250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455928026881 / 20000000000000 : ℝ))
      (E := (cell12479 ⟨23, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (208198974723 / 250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455928026881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_24 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20811277513541 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279644116807 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨24, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20811277513541 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279644116807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_25 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83210654457109 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569912040277 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨25, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83210654457109 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569912040277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_26 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (16635244613093 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139826077009 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨26, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (16635244613093 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139826077009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_27 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20785453961707 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279656157091 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨27, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20785453961707 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279656157091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_28 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41553716384481 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279660114849 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨28, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41553716384481 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279660114849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_29 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20768268449949 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279664146891 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨29, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20768268449949 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279664146891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_30 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83038738907423 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279668138807 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨30, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83038738907423 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279668138807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_31 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41502214030049 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139836075657 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨31, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41502214030049 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139836075657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_32 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (64820422833 / 78125000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455935225583 / 20000000000000 : ℝ))
      (E := (cell12479 ⟨32, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (64820422833 / 78125000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455935225583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_33 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82935878374427 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569920032229 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨33, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82935878374427 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569920032229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_34 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82901639473401 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279684155899 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨34, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82901639473401 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279684155899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_35 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41433712246029 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (35620127369 / 1562500000000 : ℝ))
      (E := (cell12479 ⟨35, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41433712246029 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (35620127369 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_36 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82833233399457 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279692117127 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨36, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82833233399457 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279692117127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_37 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82799066164811 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569924027981 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨37, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82799066164811 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569924027981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_38 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82764922757491 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (142481258543 / 6250000000000 : ℝ))
      (E := (cell12479 ⟨38, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82764922757491 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (142481258543 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_39 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41365401573511 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279704133177 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨39, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41365401573511 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279704133177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12480_20 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83383165970683 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139748096933 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨20, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83383165970683 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139748096933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_21 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (20837153386079 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569875053667 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨21, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (20837153386079 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569875053667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_22 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83314085454207 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (284938021217 / 12500000000000 : ℝ))
      (E := (cell12480 ⟨22, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83314085454207 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (284938021217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_23 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83279581667279 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139754089899 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨23, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83279581667279 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139754089899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_24 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (2601409442207 / 3125000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139756095241 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨24, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (2601409442207 / 3125000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139756095241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_25 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41605323435753 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279516205457 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨25, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41605323435753 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279516205457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_26 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (16635243159471 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279520169761 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨26, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (16635243159471 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279520169761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_27 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (8314180889577 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142470259059 / 6250000000000 : ℝ))
      (E := (cell12480 ⟨27, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (8314180889577 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142470259059 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_28 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41553713067257 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139764096209 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨28, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41553713067257 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139764096209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_29 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83073067481517 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279532198051 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨29, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83073067481517 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279532198051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_30 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41519366452437 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142471010267 / 6250000000000 : ℝ))
      (E := (cell12480 ⟨30, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41519366452437 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142471010267 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_31 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (2075110559321 / 2500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (11397700759 / 500000000000 : ℝ))
      (E := (cell12480 ⟨31, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (2075110559321 / 2500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (11397700759 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_32 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (16594027170767 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279544162673 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨32, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (16594027170767 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279544162673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_33 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41467936658219 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142471758759 / 6250000000000 : ℝ))
      (E := (cell12480 ⟨33, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41467936658219 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142471758759 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_34 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82901634729391 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279552144309 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨34, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82901634729391 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279552144309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_35 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82867420061593 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279556176527 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨35, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82867420061593 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279556176527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_36 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82833229282101 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139780089649 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨36, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82833229282101 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139780089649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_37 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (8279906236013 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455912830691 / 20000000000000 : ℝ))
      (E := (cell12480 ⟨37, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (8279906236013 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455912830691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_38 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (20691229816263 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279568158289 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨38, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (20691229816263 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279568158289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_39 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41365399983197 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455914427111 / 20000000000000 : ℝ))
      (E := (cell12480 ⟨39, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41365399983197 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455914427111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12481_20 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41691578396329 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279364271349 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨20, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41691578396329 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279364271349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_21 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (8334860468597 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71230258123 / 3125000000000 : ℝ))
      (E := (cell12481 ⟨21, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (8334860468597 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71230258123 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_22 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83314076915093 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455874448363 / 20000000000000 : ℝ))
      (E := (cell12481 ⟨22, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83314076915093 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455874448363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_23 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83279573446951 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71230508733 / 3125000000000 : ℝ))
      (E := (cell12481 ⟨23, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83279573446951 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71230508733 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_24 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41622547124319 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139690130067 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨24, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41622547124319 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139690130067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_25 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83210639287417 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (91175369833 / 4000000000000 : ℝ))
      (E := (cell12481 ⟨25, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83210639287417 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (91175369833 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_26 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83176208530721 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279388239959 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨26, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83176208530721 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279388239959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_27 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20785450486537 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139696122869 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨27, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20785450486537 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139696122869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_28 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83107419501463 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139698133063 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨28, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83107419501463 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139698133063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_29 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83073061164597 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279400245389 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨29, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83073061164597 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279400245389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_30 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20759681725911 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71231382639 / 3125000000000 : ℝ))
      (E := (cell12481 ⟨30, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20759681725911 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71231382639 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_31 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41502208343431 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139704132787 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨31, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41502208343431 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139704132787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_32 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82970130482671 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569853063067 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨32, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82970130482671 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569853063067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_33 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82935868259651 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279416264833 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨33, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82935868259651 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279416264833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_34 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (16580325997309 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569855061567 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨34, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (16580325997309 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569855061567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_35 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20716853908063 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139712128233 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨35, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20716853908063 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139712128233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_36 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (8283322516583 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279428237927 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨36, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (8283322516583 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279428237927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_37 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (5174941159781 / 6250000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (113971612507 / 5000000000000 : ℝ))
      (E := (cell12481 ⟨37, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (5174941159781 / 6250000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (113971612507 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_38 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82764915773623 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455887247021 / 20000000000000 : ℝ))
      (E := (cell12481 ⟨38, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82764915773623 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455887247021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_39 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (5170674799171 / 6250000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139720125957 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨39, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (5170674799171 / 6250000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139720125957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12482_20 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (10422893452043 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284904050363 / 12500000000000 : ℝ))
      (E := (cell12482 ⟨20, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (10422893452043 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284904050363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_21 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16669719165859 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (113961820881 / 5000000000000 : ℝ))
      (E := (cell12482 ⟨21, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16669719165859 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (113961820881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_22 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83314068377611 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279240426397 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨22, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83314068377611 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279240426397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_23 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (10409945653527 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (71226388543 / 3125000000000 : ℝ))
      (E := (cell12482 ⟨23, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (10409945653527 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (71226388543 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_24 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16649017269641 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139624192057 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨24, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16649017269641 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139624192057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_25 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41605315852421 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279252398957 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨25, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41605315852421 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279252398957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_26 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83176201265561 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279256423009 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨26, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83176201265561 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279256423009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_27 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83141794997961 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (45585208021 / 2000000000000 : ℝ))
      (E := (cell12482 ⟨27, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83141794997961 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (45585208021 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_28 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (5194213304363 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142454024651 / 6250000000000 : ℝ))
      (E := (cell12482 ⟨28, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (5194213304363 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142454024651 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_29 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83073054849033 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279268405841 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨29, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83073054849033 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279268405841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_30 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (20759680225933 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279272379333 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨30, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (20759680225933 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279272379333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_31 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83004411002163 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139638187803 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨31, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83004411002163 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139638187803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_32 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82970125112747 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279280396699 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨32, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82970125112747 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279280396699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_33 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41467931602033 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (113964219293 / 5000000000000 : ℝ))
      (E := (cell12482 ⟨33, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41467931602033 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (113964219293 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_34 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82901625244861 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279288403189 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨34, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82901625244861 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279288403189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_35 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16573482240807 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227929239143 / 10000000000000 : ℝ))
      (E := (cell12482 ⟨35, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16573482240807 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227929239143 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_36 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16566644210129 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279296410277 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨36, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16566644210129 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279296410277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_37 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (8279905475391 / 10000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284912550247 / 12500000000000 : ℝ))
      (E := (cell12482 ⟨37, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (8279905475391 / 10000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284912550247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_38 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41382456141601 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (71228261473 / 3125000000000 : ℝ))
      (E := (cell12482 ⟨38, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41382456141601 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (71228261473 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_39 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (5170674600503 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279308364849 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨39, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (5170674600503 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279308364849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12483_20 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (4169156922087 / 5000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279100588533 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨20, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (4169156922087 / 5000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279100588533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_21 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83348586974291 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139552285581 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨21, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83348586974291 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139552285581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_22 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (520712874011 / 625000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279108606877 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨22, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (520712874011 / 625000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279108606877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_23 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (650621539149 / 781250000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279112583237 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨23, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (650621539149 / 781250000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279112583237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_24 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (20811269612331 / 25000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (91164664831 / 4000000000000 : ℝ))
      (E := (cell12483 ⟨24, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (20811269612331 / 25000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (91164664831 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_25 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83210624123781 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279120606483 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨25, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83210624123781 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279120606483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_26 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (133081910403 / 160000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (56978115053 / 2500000000000 : ℝ))
      (E := (cell12483 ⟨26, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (133081910403 / 160000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (56978115053 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_27 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83141788051209 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279128610883 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨27, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83141788051209 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279128610883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_28 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83107406239549 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279132577291 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨28, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83107406239549 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279132577291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_29 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41536524267413 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139568281237 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨29, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41536524267413 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139568281237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_30 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41519357452569 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279140568929 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨30, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41519357452569 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279140568929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_31 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83004405318743 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (142446537433 / 6250000000000 : ℝ))
      (E := (cell12483 ⟨31, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83004405318743 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (142446537433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_32 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (1296408121001 / 1562500000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279148595967 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨32, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (1296408121001 / 1562500000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279148595967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_33 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41467929074841 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279152561789 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨33, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41467929074841 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279152561789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_34 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82901620504341 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279156556489 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨34, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82901620504341 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279156556489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_35 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41433703388471 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279160581423 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨35, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41433703388471 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279160581423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_36 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41416608468273 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455832915817 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨36, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41416608468273 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455832915817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_37 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (8279905095237 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139584304483 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨37, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (8279905095237 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139584304483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_38 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82764908793789 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455834510877 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨38, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82764908793789 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455834510877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_39 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (8273079043033 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139588295883 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨39, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (8273079043033 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139588295883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12484_20 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41691564634423 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278968828237 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨20, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41691564634423 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278968828237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_21 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (83348578120957 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569743209281 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨21, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (83348578120957 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569743209281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_22 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (4165702565377 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278976841561 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨22, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (4165702565377 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278976841561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_23 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (130124294993 / 156250000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278980845691 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨23, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (130124294993 / 156250000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278980845691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_24 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20811267637999 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284873106677 / 12500000000000 : ℝ))
      (E := (cell12484 ⟨24, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20811267637999 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284873106677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_25 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (10401327068029 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (227898881003 / 10000000000000 : ℝ))
      (E := (cell12484 ⟨25, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (10401327068029 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (227898881003 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_26 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (5198511671229 / 6250000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284874104461 / 12500000000000 : ℝ))
      (E := (cell12484 ⟨26, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (5198511671229 / 6250000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284874104461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_27 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20785445276473 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278996816817 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨27, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20785445276473 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278996816817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_28 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16621479922137 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279000814751 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨28, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16621479922137 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279000814751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_29 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (10384130277747 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279004832223 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨29, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (10384130277747 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279004832223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_30 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41519354453931 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139504406619 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨30, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41519354453931 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139504406619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_31 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41502199818301 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (227901281851 / 10000000000000 : ℝ))
      (E := (cell12484 ⟨31, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41502199818301 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (227901281851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_32 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (4148505718831 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569754212519 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨32, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (4148505718831 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569754212519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_33 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82935853096499 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139510425591 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨33, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82935853096499 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139510425591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_34 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41450807882491 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279024823341 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨34, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41450807882491 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279024823341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_35 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82867402350973 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279028826443 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨35, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82867402350973 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279028826443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_36 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20708303205883 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139516401493 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨36, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20708303205883 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139516401493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_37 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82799047151877 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284879601557 / 12500000000000 : ℝ))
      (E := (cell12484 ⟨37, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82799047151877 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (284879601557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_38 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (10345613163173 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279040796851 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨38, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (10345613163173 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279040796851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_39 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41365393626791 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279044815261 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨39, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41365393626791 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279044815261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12485_20 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83383120097661 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139418561009 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨20, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83383120097661 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139418561009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_21 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83348569269293 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139420578613 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨21, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83348569269293 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139420578613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_22 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (1666280855499 / 2000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (45576902609 / 2000000000000 : ℝ))
      (E := (cell12485 ⟨22, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (1666280855499 / 2000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (45576902609 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_23 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (2081988514539 / 2500000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139424552043 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨23, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (2081988514539 / 2500000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139424552043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_24 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83245062656219 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (227885314039 / 10000000000000 : ℝ))
      (E := (cell12485 ⟨24, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83245062656219 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (227885314039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_25 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (20802652241549 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278857126347 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨25, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (20802652241549 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278857126347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_26 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (3327047179157 / 4000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278861123717 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨26, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (3327047179157 / 4000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278861123717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_27 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83141774162009 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455773027139 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨27, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83141774162009 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455773027139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_28 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83107392983217 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139434553399 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨28, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83107392983217 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139434553399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_29 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41536517955241 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455774619631 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨29, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41536517955241 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455774619631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_30 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83038702911903 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278877112261 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨30, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83038702911903 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278877112261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_31 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (4150219697787 / 5000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278881092869 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨31, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (4150219697787 / 5000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278881092869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_32 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (5185631813151 / 6250000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139442550243 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨32, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (5185631813151 / 6250000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139442550243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_33 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82935848044517 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278889136917 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨33, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82935848044517 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278889136917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_34 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41450805513393 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139446543287 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨34, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41450805513393 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139446543287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_35 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82867397926127 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455779425299 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨35, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82867397926127 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455779425299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_36 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41416604355801 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (113945054099 / 5000000000000 : ℝ))
      (E := (cell12485 ⟨36, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41416604355801 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (113945054099 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_37 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (8279904335243 / 10000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278905129757 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨37, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (8279904335243 / 10000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278905129757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_38 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41382450908993 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139454547269 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨38, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41382450908993 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139454547269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_39 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41365392038901 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278913094039 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨39, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41365392038901 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278913094039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12486_20 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41691555464093 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569676367469 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨20, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41691555464093 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569676367469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_21 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83348560419299 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278709473189 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨21, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83348560419299 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278709473189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_22 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83314034243991 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284839184193 / 12500000000000 : ℝ))
      (E := (cell12486 ⟨22, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83314034243991 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284839184193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_23 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (8327953236919 / 10000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139358737539 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨23, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (8327953236919 / 10000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139358737539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_24 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41622527380997 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (71210046303 / 3125000000000 : ℝ))
      (E := (cell12486 ⟨24, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41622527380997 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (71210046303 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_25 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10401325173709 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278725438687 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨25, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10401325173709 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278725438687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_26 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (4158808610983 / 5000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139364733103 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨26, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (4158808610983 / 5000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139364733103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_27 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83141767219561 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91149338027 / 4000000000000 : ℝ))
      (E := (cell12486 ⟨27, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83141767219561 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91149338027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_28 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10388423294643 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278737453433 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨28, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10388423294643 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278737453433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_29 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10384128700043 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455748295441 / 20000000000000 : ℝ))
      (E := (cell12486 ⟨29, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10384128700043 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455748295441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_30 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83038696917261 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139372732999 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨30, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83038696917261 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139372732999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_31 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16600877655231 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139374740261 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨31, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16600877655231 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139374740261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_32 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (20742525911363 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91150138571 / 4000000000000 : ℝ))
      (E := (cell12486 ⟨32, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (20742525911363 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91150138571 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_33 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16587168598747 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278757477557 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨33, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16587168598747 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278757477557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_34 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82901606289751 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278761463361 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨34, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82901606289751 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278761463361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_35 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (20716848375601 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278765481577 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨35, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (20716848375601 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278765481577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_36 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82833204600757 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (22787694747 / 1000000000000 : ℝ))
      (E := (cell12486 ⟨36, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82833204600757 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (22787694747 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_37 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82799039554029 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (56969336089 / 2500000000000 : ℝ))
      (E := (cell12486 ⟨37, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82799039554029 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (56969336089 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_38 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (20691224582899 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569694361861 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨38, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (20691224582899 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569694361861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_39 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (5170673806437 / 6250000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278781428099 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨39, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (5170673806437 / 6250000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278781428099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12487_20 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83383101760419 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455714774363 / 20000000000000 : ℝ))
      (E := (cell12487 ⟨20, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83383101760419 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455714774363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_21 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41674275785487 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278577843297 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨21, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41674275785487 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278577843297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_22 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83314025714661 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139290935423 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨22, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83314025714661 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139290935423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_23 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (8327952415841 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455717168403 / 20000000000000 : ℝ))
      (E := (cell12487 ⟨23, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (8327952415841 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455717168403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_24 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (2081126171733 / 2500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139294938669 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨24, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (2081126171733 / 2500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139294938669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_25 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (4160529690733 / 5000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (11392969319 / 500000000000 : ℝ))
      (E := (cell12487 ⟨25, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (4160529690733 / 5000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (11392969319 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_26 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83176164961867 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139298931579 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨26, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83176164961867 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139298931579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_27 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16628352055709 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455720375721 / 20000000000000 : ℝ))
      (E := (cell12487 ⟨27, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16628352055709 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455720375721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_28 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16621475946493 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139302927329 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨28, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16621475946493 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139302927329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_29 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41536511645781 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278609852441 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨29, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41536511645781 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278609852441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_30 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16607738184787 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278613874453 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨30, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16607738184787 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278613874453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_31 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (10375547824731 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278617864441 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨31, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (10375547824731 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278617864441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_32 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41485049140863 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278621824371 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨32, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41485049140863 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278621824371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_33 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82935837944153 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (142414117069 / 6250000000000 : ℝ))
      (E := (cell12487 ⟨33, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82935837944153 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (142414117069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_34 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41450800776939 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569657459133 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨34, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41450800776939 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569657459133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_35 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (20716847269951 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569658458271 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨35, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (20716847269951 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569658458271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_36 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16566640098199 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455727572777 / 20000000000000 : ℝ))
      (E := (cell12487 ⟨36, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16566640098199 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455727572777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_37 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82799035756673 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278641871179 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨37, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82799035756673 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278641871179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_38 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41382447423107 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569661463893 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨38, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41382447423107 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569661463893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_39 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (1654615554583 / 2000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139324908723 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨39, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (1654615554583 / 2000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139324908723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12488_20 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (2084577314859 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139221163917 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨20, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (2084577314859 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139221163917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_21 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83348542724317 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278446325829 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨21, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83348542724317 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278446325829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_22 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83314017186961 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455690064471 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨22, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83314017186961 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455690064471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_23 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83279515949221 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278454321551 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨23, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83279515949221 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278454321551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_24 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83245038978197 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455691665463 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨24, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83245038978197 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455691665463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_25 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (2080264656029 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139231142469 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨25, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (2080264656029 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139231142469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_26 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83176157705547 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569616578643 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨26, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83176157705547 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569616578643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_27 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83141753338963 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278470302639 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨27, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83141753338963 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278470302639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_28 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (4155368655459 / 5000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278474310473 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨28, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (4155368655459 / 5000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278474310473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_29 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41536508492067 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569619570583 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨29, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41536508492067 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569619570583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_30 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41519342465963 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569620569783 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨30, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41519342465963 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569620569783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_31 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41502188460409 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (113924315157 / 5000000000000 : ℝ))
      (E := (cell12488 ⟨31, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41502188460409 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (113924315157 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_32 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41485046459619 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278490297849 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨32, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41485046459619 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278490297849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_33 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82935832895771 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569623566249 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨33, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82935832895771 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569623566249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_34 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (16580319363833 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139249132337 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨34, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (16580319363833 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139249132337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_35 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41433692329163 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278502298233 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨35, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41433692329163 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278502298233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_36 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41416598191159 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455701261633 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨36, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41416598191159 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455701261633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_37 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41399515980181 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278510295301 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨37, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41399515980181 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278510295301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_38 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82764891361837 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569628565061 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨38, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82764891361837 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569628565061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_39 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (20682693639069 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278518262077 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨39, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (20682693639069 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278518262077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12489_20 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83383083430009 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278310779677 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨20, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83383083430009 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278310779677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_21 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83348533879329 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139157402113 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨21, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83348533879329 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139157402113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_22 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83314008660889 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278318769771 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨22, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83314008660889 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278318769771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_23 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83279507741621 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (284790349629 / 12500000000000 : ℝ))
      (E := (cell12489 ⟨23, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83279507741621 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (284790349629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_24 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (5202814443039 / 6250000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278326773279 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨24, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (5202814443039 / 6250000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278326773279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_25 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (8321057866917 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139165380239 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨25, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (8321057866917 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139165380239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_26 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41588075225349 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139167381027 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨26, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41588075225349 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139167381027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_27 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41570873200407 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139169390601 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨27, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41570873200407 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139169390601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_28 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83107366487289 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455668552487 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨28, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83107366487289 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455668552487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_29 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41536505339031 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569586691719 / 25000000000000 : ℝ))
      (E := (cell12489 ⟨29, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41536505339031 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569586691719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_30 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (5189917433827 / 6250000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139175398511 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨30, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (5189917433827 / 6250000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139175398511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_31 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41502185622533 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278354796619 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨31, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41502185622533 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278354796619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_32 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82970087557989 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (142397422977 / 6250000000000 : ℝ))
      (E := (cell12489 ⟨32, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82970087557989 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (142397422977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_33 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82935827848589 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278362770357 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨33, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82935827848589 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278362770357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_34 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82901592085613 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278366806373 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨34, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82901592085613 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278366806373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_35 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (8286738023797 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278370759807 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨35, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (8286738023797 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278370759807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_36 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (20708298068681 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (284796850943 / 12500000000000 : ℝ))
      (E := (cell12489 ⟨36, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (20708298068681 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (284796850943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_37 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82799028165097 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278378774583 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨37, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82799028165097 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278378774583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_38 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (20691221969617 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278382778817 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨38, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (20691221969617 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278382778817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_39 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82730771384371 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455677352399 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨39, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82730771384371 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455677352399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12490_20 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (16676614853473 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278179343861 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨20, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (16676614853473 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278179343861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_21 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83348525036009 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278183336771 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨21, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83348525036009 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278183336771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_22 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41657000068223 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139093664851 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨22, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41657000068223 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139093664851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_23 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (8327949953561 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278191326789 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨23, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (8327949953561 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278191326789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_24 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83245023200601 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278195331933 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨24, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83245023200601 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278195331933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_25 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (20802642774673 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278199348793 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨25, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (20802642774673 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278199348793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_26 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83176143197321 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2847754153 / 125000000000 : ℝ))
      (E := (cell12490 ⟨26, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83176143197321 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2847754153 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_27 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83141739464097 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139103657147 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨27, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83141739464097 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139103657147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_28 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (10388419983349 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139105663717 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨28, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (10388419983349 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139105663717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_29 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83073004373343 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278215306079 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨29, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83073004373343 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278215306079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_30 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41519336475927 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278219311141 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨30, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41519336475927 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278219311141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_31 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (8300436557059 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278223344883 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨31, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (8300436557059 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278223344883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_32 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82970082197977 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139113675401 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨32, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82970082197977 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139113675401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_33 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (16587164560521 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (227823133063 / 10000000000000 : ℝ))
      (E := (cell12490 ⟨33, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (16587164560521 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (227823133063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_34 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41450793676611 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139117672229 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨34, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41450793676611 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139117672229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_35 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (5179210988671 / 6250000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278239335027 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨35, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (5179210988671 / 6250000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278239335027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_36 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82833188168213 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278243303389 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨36, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82833188168213 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278243303389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_37 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (20699756092719 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569561827257 / 25000000000000 : ℝ))
      (E := (cell12490 ⟨37, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (20699756092719 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569561827257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_38 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (10345610549513 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139125646969 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨38, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (10345610549513 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139125646969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_39 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82730768213433 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278255317201 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨39, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82730768213433 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278255317201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12491_20 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83383065106429 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278047962129 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨20, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83383065106429 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278047962129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_21 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (20837129048589 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284756490433 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨21, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (20837129048589 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284756490433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_22 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83313991613631 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (455611188769 / 20000000000000 : ℝ))
      (E := (cell12491 ⟨22, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83313991613631 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (455611188769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_23 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83279491331187 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278059910823 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨23, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83279491331187 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278059910823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_24 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83245015314127 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139031972463 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨24, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83245015314127 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139031972463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_25 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83210563529723 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139033966569 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨25, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83210563529723 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139033966569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_26 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16635227189083 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569517984303 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨26, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16635227189083 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569517984303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_27 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (20785433132203 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569518975479 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨27, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (20785433132203 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569518975479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_28 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83107353247687 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569519986757 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨28, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83107353247687 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569519986757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_29 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83072998069979 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139041949969 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨29, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83072998069979 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139041949969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_30 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83038666963791 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284760992309 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨30, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83038666963791 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284760992309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_31 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (8300435989739 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284761486177 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨31, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (8300435989739 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284761486177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_32 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82970076839203 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278095930281 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨32, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82970076839203 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278095930281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_33 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (4146790887891 / 5000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278099887251 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨33, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (4146790887891 / 5000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278099887251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_34 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82901582621991 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139051968759 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨34, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82901582621991 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139051968759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_35 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82867371400623 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (91124316267 / 4000000000000 : ℝ))
      (E := (cell12491 ⟨35, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82867371400623 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (91124316267 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_36 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16566636812557 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278111912967 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨36, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16566636812557 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278111912967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_37 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82799020577699 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569528974659 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨37, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82799020577699 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569528974659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_38 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82764880914747 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278119922963 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨38, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82764880914747 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278119922963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_39 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82730765043463 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142382745481 / 6250000000000 : ℝ))
      (E := (cell12491 ⟨39, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82730765043463 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142382745481 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12492_20 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41691527973599 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138958288113 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨20, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41691527973599 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138958288113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_21 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (8334850735437 / 10000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138960282153 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨21, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (8334850735437 / 10000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138960282153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_22 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20828495773111 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277924553897 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨22, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20828495773111 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277924553897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_23 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83279483128353 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277928549133 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨23, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83279483128353 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277928549133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_24 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41622503714601 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227793255391 / 10000000000000 : ℝ))
      (E := (cell12492 ⟨24, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41622503714601 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227793255391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_25 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (10401319495283 / 12500000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142371035743 / 6250000000000 : ℝ))
      (E := (cell12492 ⟨25, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (10401319495283 / 12500000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142371035743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_26 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (4158806434749 / 5000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455588109619 / 20000000000000 : ℝ))
      (E := (cell12492 ⟨26, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (4158806434749 / 5000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455588109619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_27 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83141725594959 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277944544071 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨27, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83141725594959 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277944544071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_28 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (3324293865199 / 4000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277948562773 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨28, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (3324293865199 / 4000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277948562773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_29 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (2596030992749 / 3125000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284744068557 / 12500000000000 : ℝ))
      (E := (cell12492 ⟨29, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (2596030992749 / 3125000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284744068557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_30 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83038660977043 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277956562033 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨30, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83038660977043 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277956562033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_31 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (16600870845093 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277960547251 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨31, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (16600870845093 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277960547251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_32 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41485035740833 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (17796598161 / 781250000000 : ℝ))
      (E := (cell12492 ⟨32, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41485035740833 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (17796598161 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_33 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82935812714233 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138984278673 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨33, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82935812714233 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138984278673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_34 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82901577891919 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138986292777 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨34, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82901577891919 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138986292777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_35 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (5179210436477 / 6250000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277976533361 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨35, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (5179210436477 / 6250000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277976533361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_36 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82833179958439 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277980577647 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨36, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82833179958439 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277980577647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_37 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82799016785567 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142374033963 / 6250000000000 : ℝ))
      (E := (cell12492 ⟨37, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82799016785567 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142374033963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_38 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (16552975486879 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277988548537 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨38, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (16552975486879 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277988548537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_39 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (4136538093723 / 5000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138996267389 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨39, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (4136538093723 / 5000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138996267389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12493_20 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83383046789673 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (227778524441 / 10000000000000 : ℝ))
      (E := (cell12493 ⟨20, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83383046789673 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (227778524441 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_21 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (1666969970321 / 2000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (22777892593 / 1000000000000 : ℝ))
      (E := (cell12493 ⟨21, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (1666969970321 / 2000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (22777892593 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_22 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83313974572883 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277793276469 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨22, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83313974572883 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277793276469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_23 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83279474927107 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277797241721 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨23, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83279474927107 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277797241721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_24 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41622499772913 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138900637793 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨24, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41622499772913 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138900637793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_25 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16642109679263 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277805265043 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨25, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16642109679263 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277805265043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_26 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16635224289203 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138904635923 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨26, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16635224289203 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138904635923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_27 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (10392714832817 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277813240759 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨27, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (10392714832817 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277813240759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_28 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16621468002731 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138908616557 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨28, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16621468002731 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138908616557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_29 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83072985467311 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138910625817 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨29, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83072985467311 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138910625817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_30 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83038654991609 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138912620159 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨30, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83038654991609 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138912620159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_31 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83004348554817 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277829259871 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨31, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83004348554817 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277829259871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_32 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16594013225073 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138916626893 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨32, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16594013225073 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138916626893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_33 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16587161534369 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277837223791 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨33, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16587161534369 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277837223791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_34 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82901573163007 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277841229979 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨34, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82901573163007 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277841229979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_35 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82867362567761 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (71182664803 / 3125000000000 : ℝ))
      (E := (cell12493 ⟨35, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82867362567761 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (71182664803 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_36 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (10354146981897 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569462309699 / 25000000000000 : ℝ))
      (E := (cell12493 ⟨36, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (10354146981897 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569462309699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_37 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41399506497239 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138926621673 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨37, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41399506497239 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138926621673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_38 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (10345609244381 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277857229339 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨38, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (10345609244381 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277857229339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_39 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (10341344838303 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138930627927 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨39, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (10341344838303 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138930627927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12494_20 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41691518816927 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (113882701247 / 5000000000000 : ℝ))
      (E := (cell12494 ⟨20, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41691518816927 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (113882701247 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_21 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83348489679397 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138829004223 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨21, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83348489679397 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138829004223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_22 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (1666279321099 / 2000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284707749369 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨22, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (1666279321099 / 2000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284707749369 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_23 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (10409933340931 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277665988591 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨23, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (10409933340931 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277665988591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_24 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41622495831999 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284708749157 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨24, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41622495831999 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284708749157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_25 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41605270415937 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (35588656447 / 1562500000000 : ℝ))
      (E := (cell12494 ⟨25, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41605270415937 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (35588656447 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_26 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (2079402854963 / 2500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227767799167 / 10000000000000 : ℝ))
      (E := (cell12494 ⟨26, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (2079402854963 / 2500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227767799167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_27 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (16628342346309 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138840995991 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨27, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (16628342346309 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138840995991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_28 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83107333398727 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277686016499 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨28, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83107333398727 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277686016499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_29 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41536489584003 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91107600379 / 4000000000000 : ℝ))
      (E := (cell12494 ⟨29, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41536489584003 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91107600379 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_30 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83038649007489 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (142355873333 / 6250000000000 : ℝ))
      (E := (cell12494 ⟨30, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83038649007489 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (142355873333 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_31 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (20751085721361 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455539593753 / 20000000000000 : ℝ))
      (E := (cell12494 ⟨31, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (20751085721361 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455539593753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_32 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82970060770301 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455540399563 / 20000000000000 : ℝ))
      (E := (cell12494 ⟨32, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82970060770301 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455540399563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_33 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41467901315327 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455541200743 / 20000000000000 : ℝ))
      (E := (cell12494 ⟨33, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41467901315327 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455541200743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_34 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82901568435253 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227770998797 / 10000000000000 : ℝ))
      (E := (cell12494 ⟨34, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82901568435253 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227770998797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_35 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (8286735815301 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (71178562827 / 3125000000000 : ℝ))
      (E := (cell12494 ⟨35, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (8286735815301 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (71178562827 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_36 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41416585876497 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277718013683 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨36, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41416585876497 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277718013683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_37 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (5174938075277 / 6250000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569430499613 / 25000000000000 : ℝ))
      (E := (cell12494 ⟨37, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (5174938075277 / 6250000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569430499613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_38 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41382435238353 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277725965371 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨38, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41382435238353 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277725965371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_39 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41365377769677 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277729973521 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨39, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41365377769677 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277729973521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12495_20 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (4169151423987 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138761400651 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨20, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (4169151423987 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138761400651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_21 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83348480844409 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138763405873 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨21, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83348480844409 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138763405873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_22 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83313957538643 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277530825957 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨22, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83313957538643 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277530825957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_23 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83279458529377 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (113876739487 / 5000000000000 : ℝ))
      (E := (cell12495 ⟨23, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83279458529377 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (113876739487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_24 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41622491891859 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (227753876527 / 10000000000000 : ℝ))
      (E := (cell12495 ⟨24, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41622491891859 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (227753876527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_25 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83210533268943 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277542814579 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨25, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83210533268943 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277542814579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_26 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41588053476247 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138773382983 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨26, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41588053476247 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138773382983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_27 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (1299089137531 / 1562500000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277550797741 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨27, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (1299089137531 / 1562500000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277550797741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_28 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (8310732678519 / 10000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138777398019 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨28, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (8310732678519 / 10000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138777398019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_29 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41536486435027 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277558763509 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨29, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41536486435027 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277558763509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_30 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41519321512341 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455512552213 / 20000000000000 : ℝ))
      (E := (cell12495 ⟨30, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41519321512341 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455512552213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_31 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16600867443469 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569391697741 / 25000000000000 : ℝ))
      (E := (cell12495 ⟨31, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16600867443469 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569391697741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_32 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82970055416473 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277570796697 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨32, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82970055416473 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277570796697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_33 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (4146789879533 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284696847499 / 12500000000000 : ℝ))
      (E := (cell12495 ⟨33, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (4146789879533 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284696847499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_34 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82901563708659 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138789400469 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨34, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82901563708659 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138789400469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_35 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (4143367686969 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (71174462571 / 3125000000000 : ℝ))
      (E := (cell12495 ⟨35, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (4143367686969 / 5000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (71174462571 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_36 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16566633530379 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (28469834813 / 1250000000000 : ℝ))
      (E := (cell12495 ⟨36, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16566633530379 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (28469834813 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_37 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (8279900541543 / 10000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569397702181 / 25000000000000 : ℝ))
      (E := (cell12495 ⟨37, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (8279900541543 / 10000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569397702181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_38 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82764866999369 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277594756633 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨38, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82764866999369 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277594756633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_39 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82730752373251 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (35587481331 / 1562500000000 : ℝ))
      (E := (cell12495 ⟨39, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82730752373251 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (35587481331 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12496_20 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83383019327331 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455478326351 / 20000000000000 : ℝ))
      (E := (cell12496 ⟨20, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83383019327331 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455478326351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_21 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83348472011087 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (5693489173 / 250000000000 : ℝ))
      (E := (cell12496 ⟨21, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83348472011087 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (5693489173 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_22 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83313949023961 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277399652877 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨22, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83313949023961 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277399652877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_23 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20819862583223 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277403645173 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨23, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20819862583223 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277403645173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_24 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (16648995180997 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277407649983 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨24, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (16648995180997 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277407649983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_25 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83210525707519 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138705806293 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨25, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83210525707519 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138705806293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_26 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41588049853969 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277415653133 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨26, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41588049853969 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277415653133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_27 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41570848936927 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569354914509 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨27, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41570848936927 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569354914509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_28 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (16621464034609 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277423630177 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨28, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (16621464034609 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277423630177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_29 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41536483286727 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569356907669 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨29, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41536483286727 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569356907669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_30 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83038637043189 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284678950441 / 12500000000000 : ℝ))
      (E := (cell12496 ⟨30, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83038637043189 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284678950441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_31 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83004331550521 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277435609437 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨31, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83004331550521 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277435609437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_32 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82970050063881 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (17792497269 / 781250000000 : ℝ))
      (E := (cell12496 ⟨32, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82970050063881 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (17792497269 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_33 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (10366974068983 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455488722237 / 20000000000000 : ℝ))
      (E := (cell12496 ⟨33, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (10366974068983 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455488722237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_34 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41450779491611 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277447610301 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨34, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41450779491611 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277447610301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_35 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82867349326869 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569362912281 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨35, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82867349326869 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569362912281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_36 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20708290887969 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (142340975719 / 6250000000000 : ℝ))
      (E := (cell12496 ⟨36, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20708290887969 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (142340975719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_37 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (8279900162747 / 10000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (227745961551 / 10000000000000 : ℝ))
      (E := (cell12496 ⟨37, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (8279900162747 / 10000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (227745961551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_38 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20691215880759 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284682950391 / 12500000000000 : ℝ))
      (E := (cell12496 ⟨38, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20691215880759 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284682950391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_39 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41365374604057 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138733816719 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨39, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41365374604057 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138733816719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12497_20 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41691505088313 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277260516299 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨20, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41691505088313 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277260516299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_21 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83348463179429 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277264522529 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨21, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83348463179429 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277264522529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_22 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16662788102181 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (8895580211 / 390625000000 : ℝ))
      (E := (cell12497 ⟨22, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16662788102181 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (8895580211 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_23 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83279442137993 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (284659069361 / 12500000000000 : ℝ))
      (E := (cell12497 ⟨23, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83279442137993 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (284659069361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_24 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (416224840139 / 500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277276530689 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨24, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (416224840139 / 500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277276530689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_25 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (20802629536901 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138640261689 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨25, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (20802629536901 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138640261689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_26 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (1663521849297 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (284660567047 / 12500000000000 : ℝ))
      (E := (cell12497 ⟨26, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (1663521849297 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (284660567047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_27 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83141690947153 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138644257223 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨27, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83141690947153 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138644257223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_28 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (8310731356229 / 10000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277292518917 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨28, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (8310731356229 / 10000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277292518917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_29 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41536480139103 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138648247019 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨29, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41536480139103 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138648247019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_30 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83038631063009 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277300500719 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨30, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83038631063009 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277300500719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_31 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83004325884971 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277304541217 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨31, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83004325884971 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277304541217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_32 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (3318801788501 / 4000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277308500481 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨32, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (3318801788501 / 4000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277308500481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_33 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (10366973439283 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (142332031081 / 6250000000000 : ℝ))
      (E := (cell12497 ⟨33, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (10366973439283 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (142332031081 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_34 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (80958549081 / 97656250000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (227731653323 / 10000000000000 : ℝ))
      (E := (cell12497 ⟨34, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (80958549081 / 97656250000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (227731653323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_35 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41433672457739 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277320492409 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨35, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41433672457739 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277320492409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_36 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41416579726469 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91092979723 / 4000000000000 : ℝ))
      (E := (cell12497 ⟨36, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41416579726469 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91092979723 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_37 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82798997840553 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277328536121 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨37, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82798997840553 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277328536121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_38 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (20691215011927 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138666252427 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨38, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (20691215011927 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138666252427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_39 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41365373021971 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569334129247 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨39, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41365373021971 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569334129247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12498_20 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (10422875128453 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138564727469 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨20, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (10422875128453 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138564727469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_21 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (20837113587359 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277133488297 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨21, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (20837113587359 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277133488297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_22 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (3332557279979 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (35580272959 / 1562500000000 : ℝ))
      (E := (cell12498 ⟨22, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (3332557279979 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (35580272959 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_23 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (2081985848617 / 2500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277141460561 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨23, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (2081985848617 / 2500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277141460561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_24 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83244960152161 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455429093149 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨24, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83244960152161 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455429093149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_25 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16642102117839 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284643686073 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨25, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16642102117839 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284643686073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_26 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83176085223231 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (142322092131 / 6250000000000 : ℝ))
      (E := (cell12498 ⟨26, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83176085223231 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (142322092131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_27 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83141684021881 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (113857874191 / 5000000000000 : ℝ))
      (E := (cell12498 ⟨27, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83141684021881 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (113857874191 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_28 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (3324292278117 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277161462261 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨28, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (3324292278117 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277161462261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_29 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83072953984309 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284645683817 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨29, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83072953984309 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284645683817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_30 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41519312542071 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (14232309079 / 625000000000 : ℝ))
      (E := (cell12498 ⟨30, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41519312542071 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (14232309079 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_31 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16600864044139 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (91086938771 / 4000000000000 : ℝ))
      (E := (cell12498 ⟨31, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16600864044139 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (91086938771 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_32 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82970039362403 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284647182991 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨32, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82970039362403 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284647182991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_33 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82935782477861 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138590719163 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨33, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82935782477861 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138590719163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_34 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (5181346845989 / 6250000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569296363139 / 25000000000000 : ℝ))
      (E := (cell12498 ⟨34, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (5181346845989 / 6250000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569296363139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_35 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82867340505207 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277189449349 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨35, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82867340505207 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277189449349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_36 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82833155355081 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455438685951 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨36, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82833155355081 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455438685951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_37 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41399497027339 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (35581210207 / 1562500000000 : ℝ))
      (E := (cell12498 ⟨37, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41399497027339 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (35581210207 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_38 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82764856573383 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284650182727 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨38, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82764856573383 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284650182727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_39 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (2585335715023 / 3125000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455441091167 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨39, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (2585335715023 / 3125000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455441091167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12499_20 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41691495940163 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284624805959 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨20, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41691495940163 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284624805959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_21 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41674222760553 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277002449943 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨21, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41674222760553 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277002449943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_22 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20828480872417 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (28462580737 / 1250000000000 : ℝ))
      (E := (cell12499 ⟨22, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20828480872417 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (28462580737 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_23 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (10409928219119 / 12500000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (45540209577 / 2000000000000 : ℝ))
      (E := (cell12499 ⟨23, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (10409928219119 / 12500000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (45540209577 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_24 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20811238069517 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142313403447 / 6250000000000 : ℝ))
      (E := (cell12499 ⟨24, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20811238069517 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142313403447 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_25 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41605251516147 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569254612457 / 25000000000000 : ℝ))
      (E := (cell12499 ⟨25, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41605251516147 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569254612457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_26 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83176077983079 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138511233147 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨26, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83176077983079 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138511233147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_27 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41570838549019 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (71157076541 / 3125000000000 : ℝ))
      (E := (cell12499 ⟨27, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41570838549019 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (71157076541 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_28 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83107300344951 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142314403763 / 6250000000000 : ℝ))
      (E := (cell12499 ⟨28, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83107300344951 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142314403763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_29 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20768236922941 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (71157326351 / 3125000000000 : ℝ))
      (E := (cell12499 ⟨29, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20768236922941 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (71157326351 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_30 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83038619106587 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569259614823 / 25000000000000 : ℝ))
      (E := (cell12499 ⟨30, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83038619106587 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569259614823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_31 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20751078639423 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277042452127 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨31, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20751078639423 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277042452127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_32 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20742508503379 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569261605923 / 25000000000000 : ℝ))
      (E := (cell12499 ⟨32, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20742508503379 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569261605923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_33 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82935777442653 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138525217139 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨33, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82935777442653 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138525217139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_34 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82901544813861 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (455410885373 / 20000000000000 : ℝ))
      (E := (cell12499 ⟨34, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82901544813861 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (455410885373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_35 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41433668048027 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138529230669 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨35, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41433668048027 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138529230669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_36 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16566630251661 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284632802693 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨36, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16566630251661 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284632802693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_37 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16559798053969 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277066425547 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨37, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16559798053969 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277066425547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_38 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82764853100061 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138535207667 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨38, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82764853100061 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138535207667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_39 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16546147943699 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277074449981 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨39, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16546147943699 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277074449981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

end BstLean.Part268
