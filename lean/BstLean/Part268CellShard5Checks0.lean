import BstLean.Part268CellShard5Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12475_0 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (10509931997383 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140038303627 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨0, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (10509931997383 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140038303627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_1 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (84044407964357 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280080587091 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨1, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (84044407964357 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280080587091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_2 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (84009384987301 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570021148369 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨2, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (84009384987301 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570021148369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_3 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (2624199594099 / 3125000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140044288947 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨3, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (2624199594099 / 3125000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140044288947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_4 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83939413999419 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (28501156867 / 1250000000000 : ℝ))
      (E := (cell12475 ⟨4, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83939413999419 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (28501156867 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_5 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83904465915713 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280096574527 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨5, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83904465915713 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280096574527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_6 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (16773908544779 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228010054611 / 10000000000000 : ℝ))
      (E := (cell12475 ⟨6, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (16773908544779 / 20000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228010054611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_7 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (20958661097001 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140052294089 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨7, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (20958661097001 / 25000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140052294089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_8 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41899885436133 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (142506783429 / 6250000000000 : ℝ))
      (E := (cell12475 ⟨8, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41899885436133 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (142506783429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_9 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83764922141097 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280112567747 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨9, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83764922141097 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280112567747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_10 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83730098159097 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456023315667 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨10, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83730098159097 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456023315667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_11 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83695298891051 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280120573781 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨11, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83695298891051 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280120573781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_12 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83660524301931 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228012456099 / 10000000000000 : ℝ))
      (E := (cell12475 ⟨12, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83660524301931 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228012456099 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_13 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (10453221794611 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280128546617 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨13, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (10453221794611 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280128546617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_14 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83591049021259 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140066268533 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨14, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83591049021259 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140066268533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_15 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83556348260557 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280136538497 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨15, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83556348260557 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280136538497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_16 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83521672040477 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (91205622273 / 4000000000000 : ℝ))
      (E := (cell12475 ⟨16, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83521672040477 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (91205622273 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_17 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83487020326893 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (285018067441 / 12500000000000 : ℝ))
      (E := (cell12475 ⟨17, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83487020326893 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (285018067441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_18 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (83452393085853 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280148550171 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨18, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (83452393085853 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280148550171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_19 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (1303402973181 / 1562500000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280152535701 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨19, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (1303402973181 / 1562500000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280152535701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12476_0 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16815888059931 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (227994440913 / 10000000000000 : ℝ))
      (E := (cell12476 ⟨0, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16815888059931 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (227994440913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_1 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (84044392613961 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279948399277 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨1, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (84044392613961 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279948399277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_2 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (84009369965453 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279952416761 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨2, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (84009369965453 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279952416761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_3 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83974372317401 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (455991282613 / 20000000000000 : ℝ))
      (E := (cell12476 ⟨3, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83974372317401 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (455991282613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_4 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83939399633271 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279960397201 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨4, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83939399633271 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279960397201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_5 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83904451876719 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (7124888681 / 312500000000 : ℝ))
      (E := (cell12476 ⟨5, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83904451876719 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (7124888681 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_6 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83869529011593 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142498026353 / 6250000000000 : ℝ))
      (E := (cell12476 ⟨6, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83869529011593 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142498026353 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_7 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41917315500967 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279972362837 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨7, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41917315500967 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279972362837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_8 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (327342803953 / 390625000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1139988191627 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨8, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (327342803953 / 390625000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1139988191627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_9 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (8376490940611 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279980374703 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨9, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (8376490940611 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279980374703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_10 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (20932521437241 / 25000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279984402609 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨10, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (20932521437241 / 25000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279984402609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_11 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16739057361063 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (569997089527 / 25000000000000 : ℝ))
      (E := (cell12476 ⟨11, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16739057361063 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (569997089527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_12 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16732102508027 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (227999236417 / 10000000000000 : ℝ))
      (E := (cell12476 ⟨12, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16732102508027 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (227999236417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_13 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83625762918577 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279996369427 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨13, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83625762918577 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2279996369427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_14 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41795518952989 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280000380283 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨14, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41795518952989 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280000380283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_15 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83556337467853 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140002172379 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨15, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83556337467853 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140002172379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_16 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83521661569899 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (285001048127 / 12500000000000 : ℝ))
      (E := (cell12476 ⟨16, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83521661569899 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (285001048127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_17 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (83487010177987 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140006166121 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨17, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (83487010177987 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140006166121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_18 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (8345238325817 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (114000818317 / 5000000000000 : ℝ))
      (E := (cell12476 ⟨18, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (8345238325817 / 10000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (114000818317 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_19 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41708890388337 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280020376097 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨19, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41708890388337 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280020376097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12477_0 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (42039712311381 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455962464313 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨0, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (42039712311381 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455962464313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_1 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (84044377266041 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279816322111 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨1, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (84044377266041 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279816322111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_2 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (84009354946039 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279820292949 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨2, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (84009354946039 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279820292949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_3 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83974357626029 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279824301203 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨3, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83974357626029 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279824301203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_4 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20984846317369 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (91193131923 / 4000000000000 : ℝ))
      (E := (cell12477 ⟨4, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20984846317369 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (91193131923 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_5 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41952218920019 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569958073079 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨5, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41952218920019 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569958073079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_6 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16773903060313 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (113991814621 / 5000000000000 : ℝ))
      (E := (cell12477 ⟨6, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16773903060313 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (113991814621 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_7 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83834617618097 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279840248673 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨7, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83834617618097 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279840248673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_8 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83799744753861 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279844284937 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨8, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83799744753861 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279844284937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_9 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20941224168319 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569962073253 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨9, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20941224168319 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569962073253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_10 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83730073340943 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455970456061 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨10, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83730073340943 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455970456061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_11 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (1673905494433 / 2000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (142491015873 / 6250000000000 : ℝ))
      (E := (cell12477 ⟨11, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (1673905494433 / 2000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (142491015873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_12 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (8366050078037 / 10000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227986027897 / 10000000000000 : ℝ))
      (E := (cell12477 ⟨12, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (8366050078037 / 10000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (227986027897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_13 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83625751482257 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279864245853 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨13, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83625751482257 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279864245853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_14 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83591026792649 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279868277179 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨14, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83591026792649 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279868277179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_15 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41778163338531 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (22798722629 / 1000000000000 : ℝ))
      (E := (cell12477 ⟨15, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41778163338531 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (22798722629 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_16 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (10440206387649 / 12500000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139938133509 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨16, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (10440206387649 / 12500000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139938133509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_17 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41743500015457 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279880237013 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨17, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41743500015457 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279880237013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_18 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (2086309335807 / 2500000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139942118223 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨18, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (2086309335807 / 2500000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139942118223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_19 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (83417771271517 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279888212263 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨19, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (83417771271517 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279888212263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12478_0 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (2627481529637 / 3125000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279680228989 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨0, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (2627481529637 / 3125000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279680228989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_1 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (21011090480149 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284960529997 / 12500000000000 : ℝ))
      (E := (cell12478 ⟨1, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (21011090480149 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284960529997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_2 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (4200466996453 / 5000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139844111021 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨2, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (4200466996453 / 5000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139844111021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_3 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83974342937051 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284961530289 / 12500000000000 : ℝ))
      (E := (cell12478 ⟨3, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83974342937051 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284961530289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_4 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (16787874181607 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284962024263 / 12500000000000 : ℝ))
      (E := (cell12478 ⟨4, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (16787874181607 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284962024263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_5 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83904423805671 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569925050477 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨5, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83904423805671 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569925050477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_6 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83869501593809 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279704216359 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨6, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83869501593809 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279704216359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_7 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83834604236491 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279708187741 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨7, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83834604236491 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279708187741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_8 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83799731697947 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279712181941 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨8, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83799731697947 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279712181941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_9 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (1308826311603 / 1562500000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139858103343 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨9, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (1308826311603 / 1562500000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139858103343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_10 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83730060935033 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139860105713 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨10, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83730060935033 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139860105713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_11 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (10461907830007 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569931050829 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨11, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (10461907830007 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569931050829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_12 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (20915122255659 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284966023657 / 12500000000000 : ℝ))
      (E := (cell12478 ⟨12, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (20915122255659 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (284966023657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_13 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83625740047929 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279732175897 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨13, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83625740047929 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279732175897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_14 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83591015681271 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569934042411 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨14, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83591015681271 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569934042411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_15 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83556315888181 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569935044163 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨15, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83556315888181 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569935044163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_16 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (20880410158589 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (142484012677 / 6250000000000 : ℝ))
      (E := (cell12478 ⟨16, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (20880410158589 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (142484012677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_17 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (10435873735709 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139874097831 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨17, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (10435873735709 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139874097831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_18 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (83452363608181 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279752160493 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨18, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (83452363608181 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279752160493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_19 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (5213610110507 / 6250000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455951232133 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨19, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (5213610110507 / 6250000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455951232133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12479_0 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (84079393276523 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569887061743 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨0, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (84079393276523 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569887061743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_1 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (672354772621 / 800000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (56988805267 / 2500000000000 : ℝ))
      (E := (cell12479 ⟨1, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (672354772621 / 800000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (56988805267 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_2 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (16801864982903 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279556204039 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨2, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (16801864982903 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279556204039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_3 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83974328250467 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569890044633 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨3, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83974328250467 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569890044633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_4 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83939356548947 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (284945525131 / 12500000000000 : ℝ))
      (E := (cell12479 ⟨4, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83939356548947 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (284945525131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_5 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (5244025610851 / 6250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279568222503 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨5, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (5244025610851 / 6250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279568222503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_6 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (3354779515533 / 4000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279572193461 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨6, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (3354779515533 / 4000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279572193461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_7 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41917295428559 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279576180037 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨7, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41917295428559 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279576180037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_8 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83799718644223 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139790095107 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨8, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83799718644223 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139790095107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_9 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (4188243560703 / 5000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279584173717 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨9, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (4188243560703 / 5000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279584173717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_10 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83730048531233 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279588195971 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨10, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83730048531233 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279588195971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_11 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83695250560533 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279592206153 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨11, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83695250560533 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279592206153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_12 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83660477266933 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139798076547 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨12, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83660477266933 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139798076547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_13 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83625728615591 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279600159559 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨13, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83625728615591 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279600159559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_14 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20897751142961 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139802086953 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨14, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20897751142961 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139802086953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_15 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83556305101211 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279608144151 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨15, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83556305101211 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279608144151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_16 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (5220101885587 / 6250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279612134293 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨16, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (5220101885587 / 6250000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279612134293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_17 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (83486979742261 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (45592323 / 2000000000 : ℝ))
      (E := (cell12479 ⟨17, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (83486979742261 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (45592323 / 2000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_18 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41726176892937 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279620138479 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨18, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41726176892937 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279620138479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_19 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41708876133229 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (8904781887 / 390625000000 : ℝ))
      (E := (cell12479 ⟨19, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41708876133229 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (8904781887 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12480_0 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (10509922200897 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139708129973 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨0, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (10509922200897 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139708129973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_1 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (84044331237129 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (91176809369 / 4000000000000 : ℝ))
      (E := (cell12480 ⟨1, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (84044331237129 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (91176809369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_2 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (21002327475601 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279424238943 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨2, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (21002327475601 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279424238943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_3 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (3358972542651 / 4000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139714112791 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨3, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (3358972542651 / 4000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139714112791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_4 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83939342192211 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227943226103 / 10000000000000 : ℝ))
      (E := (cell12480 ⟨4, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83939342192211 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227943226103 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_5 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (655503091749 / 781250000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279436238297 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨5, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (655503091749 / 781250000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279436238297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_6 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83869474185113 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279440223731 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨6, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83869474185113 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279440223731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_7 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (3353383099199 / 4000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279444225567 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨7, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (3353383099199 / 4000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279444225567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_8 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (8379970559269 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (284931031473 / 12500000000000 : ℝ))
      (E := (cell12480 ⟨8, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (8379970559269 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (284931031473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_9 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41882429243839 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227945219411 / 10000000000000 : ℝ))
      (E := (cell12480 ⟨9, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41882429243839 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227945219411 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_10 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (10466254516193 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279456233943 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨10, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (10466254516193 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279456233943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_11 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (2092380962077 / 2500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569865051109 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨11, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (2092380962077 / 2500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569865051109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_12 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (4183023275663 / 5000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279464228557 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨12, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (4183023275663 / 5000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279464228557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_13 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41812858592621 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139734098421 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨13, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41812858592621 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139734098421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_14 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41795496732183 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279472231853 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨14, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41795496732183 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279472231853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_15 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83556294316151 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279476223537 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨15, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83556294316151 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279476223537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_16 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83521619706297 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279480177731 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨16, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83521619706297 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279480177731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_17 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83486969600681 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (5698710541 / 250000000000 : ℝ))
      (E := (cell12480 ⟨17, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83486969600681 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (5698710541 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_18 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (83452343965357 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279488170407 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨18, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (83452343965357 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279488170407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_19 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (20854435691639 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279492161251 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨19, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (20854435691639 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279492161251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12481_0 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (84079361940343 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (22792843257 / 1000000000000 : ℝ))
      (E := (cell12481 ⟨0, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (84079361940343 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (22792843257 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_1 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (84044315899107 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139644155307 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨1, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (84044315899107 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139644155307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_2 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (3360371795709 / 4000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139646163379 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨2, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (3360371795709 / 4000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139646163379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_3 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (3358971955379 / 4000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284912040701 / 12500000000000 : ℝ))
      (E := (cell12481 ⟨3, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (3358971955379 / 4000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284912040701 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_4 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41969663918913 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279300316171 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨4, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41969663918913 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279300316171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_5 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (2097609542911 / 2500000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569826076799 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨5, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (2097609542911 / 2500000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569826076799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_6 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83869460484171 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279308307171 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨6, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83869460484171 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279308307171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_7 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41917282052531 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569828081083 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨7, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41917282052531 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569828081083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_8 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83799692543347 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279316308679 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨8, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83799692543347 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279316308679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_9 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41882422881723 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139660162933 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨9, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41882422881723 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139660162933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_10 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (16746004745993 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279324325343 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨10, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (16746004745993 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279324325343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_11 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83695226407697 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279328314257 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨11, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83695226407697 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279328314257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_12 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83660453761617 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279332299509 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨12, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83660453761617 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279332299509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_13 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20906426439221 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279336287747 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨13, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20906426439221 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279336287747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_14 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41795491179419 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569835071343 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨14, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41795491179419 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569835071343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_15 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83556283533001 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284918037317 / 12500000000000 : ℝ))
      (E := (cell12481 ⟨15, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83556283533001 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284918037317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_16 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83521609245073 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284918534373 / 12500000000000 : ℝ))
      (E := (cell12481 ⟨16, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83521609245073 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284918534373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_17 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83486959460931 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71229758703 / 3125000000000 : ℝ))
      (E := (cell12481 ⟨17, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83486959460931 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (71229758703 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_18 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (83452334146631 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279356256279 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨18, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (83452334146631 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279356256279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_19 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (16683546653681 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279360271671 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨19, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (16683546653681 / 20000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279360271671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12482_0 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (10509918284503 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279152502019 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨0, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (10509918284503 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279152502019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_1 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (84044300563557 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279156497659 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨1, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (84044300563557 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279156497659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_2 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (84009279885479 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279160467481 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨2, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (84009279885479 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279160467481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_3 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83974284205067 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142447779913 / 6250000000000 : ℝ))
      (E := (cell12482 ⟨3, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83974284205067 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142447779913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_4 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83939313485793 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279168482233 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨4, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83939313485793 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279168482233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_5 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41952183845659 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (35612070111 / 1562500000000 : ℝ))
      (E := (cell12482 ⟨5, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41952183845659 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (35612070111 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_6 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83869446785499 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279176443781 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨6, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83869446785499 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279176443781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_7 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (4191727536619 / 5000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279180476329 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨7, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (4191727536619 / 5000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279180476329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_8 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41899839748097 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142449029803 / 6250000000000 : ℝ))
      (E := (cell12482 ⟨8, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41899839748097 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (142449029803 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_9 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83764833041363 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569797113247 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨9, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83764833041363 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569797113247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_10 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16746002266499 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279192470171 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨10, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16746002266499 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279192470171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_11 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41847607167191 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279196419527 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨11, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41847607167191 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279196419527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_12 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41830221006001 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279200424019 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨12, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41830221006001 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279200424019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_13 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41812847165257 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139602216137 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨13, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41812847165257 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139602216137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_14 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (4179548562763 / 5000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279208450691 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨14, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (4179548562763 / 5000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279208450691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_15 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83556272751761 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455842485457 / 20000000000000 : ℝ))
      (E := (cell12482 ⟨15, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83556272751761 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455842485457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_16 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41760799392859 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279216426053 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨16, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41760799392859 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279216426053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_17 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (83486949323011 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227922039447 / 10000000000000 : ℝ))
      (E := (cell12482 ⟨17, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (83486949323011 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227922039447 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_18 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16690464865939 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455844879219 / 20000000000000 : ℝ))
      (E := (cell12482 ⟨18, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16690464865939 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455844879219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_19 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (20854430943001 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279228436099 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨19, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (20854430943001 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279228436099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12483_0 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (42039665307109 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569755168333 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨0, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (42039665307109 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569755168333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_1 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (84044285230479 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279024679741 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨1, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (84044285230479 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279024679741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_2 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (10501158110083 / 12500000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279028661117 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨2, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (10501158110083 / 12500000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279028661117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_3 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (1679485390561 / 2000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455806536917 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨3, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (1679485390561 / 2000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455806536917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_4 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (8393929913611 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455807328691 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨4, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (8393929913611 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455807328691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_5 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83904353668507 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139520331107 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨5, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83904353668507 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139520331107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_6 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83869433089097 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139522316781 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨6, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83869433089097 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139522316781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_7 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83834537361927 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569762155903 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨7, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83834537361927 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569762155903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_8 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (8379966645123 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279052640343 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨8, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (8379966645123 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279052640343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_9 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83764820321429 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (91162265339 / 4000000000000 : ℝ))
      (E := (cell12483 ⟨9, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83764820321429 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (91162265339 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_10 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41864999468567 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279060610409 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨10, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41864999468567 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279060610409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_11 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83695202263137 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279064636337 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨11, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83695202263137 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279064636337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_12 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (2614388445763 / 3125000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279068602089 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨12, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (2614388445763 / 3125000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279068602089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_13 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83625682906133 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139536315213 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨13, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83625682906133 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139536315213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_14 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (8359096015363 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455815322317 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨14, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (8359096015363 / 10000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455815322317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_15 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83556261972429 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569770152447 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨15, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83556261972429 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569770152447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_16 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (10440198541029 / 12500000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279084630939 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨16, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (10440198541029 / 12500000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279084630939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_17 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83486939186919 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139544311257 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨17, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83486939186919 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139544311257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_18 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83452314514549 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (71221643433 / 3125000000000 : ℝ))
      (E := (cell12483 ⟨18, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83452314514549 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (71221643433 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_19 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (83417714277353 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (142443537269 / 6250000000000 : ℝ))
      (E := (cell12483 ⟨19, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (83417714277353 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (142443537269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12484_0 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (3363172598197 / 4000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278888897427 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨0, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (3363172598197 / 4000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278888897427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_1 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (42022134949937 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569723228667 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨1, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (42022134949937 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569723228667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_2 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (2100231246957 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139448453833 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨2, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (2100231246957 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139448453833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_3 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (5248390928339 / 6250000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278900885681 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨3, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (5248390928339 / 6250000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278900885681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_4 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (83939284788777 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139452457801 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨4, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (83939284788777 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139452457801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_5 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16780867929601 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (35607951413 / 1562500000000 : ℝ))
      (E := (cell12484 ⟨5, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16780867929601 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (35607951413 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_6 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20967354848741 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569728219129 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨6, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20967354848741 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569728219129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_7 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41917261996851 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139458441043 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨7, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41917261996851 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139458441043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_8 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41899826704227 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (113946042857 / 5000000000000 : ℝ))
      (E := (cell12484 ⟨8, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41899826704227 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (113946042857 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_9 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20941201900911 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278924867329 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨9, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20941201900911 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278924867329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_10 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (2093249663597 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278928862101 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨10, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (2093249663597 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278928862101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_11 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (83695190193959 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278932848599 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨11, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (83695190193959 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278932848599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_12 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41830209259429 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278936891789 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨12, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41830209259429 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278936891789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_13 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (4181283574187 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278940882203 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨13, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (4181283574187 / 5000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278940882203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_14 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20897737263487 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (455788976857 / 20000000000000 : ℝ))
      (E := (cell12484 ⟨14, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20897737263487 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (455788976857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_15 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16711250239001 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (455789769209 / 20000000000000 : ℝ))
      (E := (cell12484 ⟨15, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16711250239001 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (455789769209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_16 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41760788936307 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278952831481 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨16, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41760788936307 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278952831481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_17 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (83486929052657 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569739211563 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨17, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (83486929052657 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569739211563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_18 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (10431538087649 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569740209391 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨18, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (10431538087649 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569740209391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_19 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20854426196113 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278964868753 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨19, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20854426196113 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2278964868753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12485_0 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (84079299298143 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569689293577 / 25000000000000 : ℝ))
      (E := (cell12485 ⟨0, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (84079299298143 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569689293577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_1 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (84044254571739 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278761202447 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨1, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (84044254571739 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278761202447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_2 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (84009234878327 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278765207129 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨2, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (84009234878327 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278765207129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_3 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83974240181187 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278769197617 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨3, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83974240181187 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278769197617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_4 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83939270443793 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (35605830983 / 1562500000000 : ℝ))
      (E := (cell12485 ⟨4, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83939270443793 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (35605830983 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_5 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (20976081407453 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278777171759 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨5, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (20976081407453 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278777171759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_6 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (838694057031 / 1000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455756234529 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨6, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (838694057031 / 1000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455756234529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_7 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41917255313853 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139392596899 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨7, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41917255313853 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139392596899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_8 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41899820183933 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139394592609 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨8, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41899820183933 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139394592609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_9 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41882397444003 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278793154553 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨9, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41882397444003 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278793154553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_10 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16745994830547 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (91151886689 / 4000000000000 : ℝ))
      (E := (cell12485 ⟨10, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16745994830547 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (91151886689 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_11 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83695178126849 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278801172403 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨11, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83695178126849 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278801172403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_12 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (2614387711729 / 3125000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278805176983 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨12, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (2614387711729 / 3125000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278805176983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_13 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16725132012667 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455761825903 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨13, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16725132012667 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455761825903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_14 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83590937956213 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (28485164407 / 1250000000000 : ℝ))
      (E := (cell12485 ⟨14, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83590937956213 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (28485164407 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_15 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83556240419489 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139408568029 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨15, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83556240419489 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139408568029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_16 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16704313483773 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139410572003 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨16, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16704313483773 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139410572003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_17 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83486918920223 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569706280969 / 25000000000000 : ℝ))
      (E := (cell12485 ⟨17, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83486918920223 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569706280969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_18 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83452294889623 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139414569611 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨18, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83452294889623 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139414569611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_19 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (83417695293299 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278833136983 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨19, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (83417695293299 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278833136983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12486_0 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (84079283643873 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278625561761 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨0, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (84079283643873 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278625561761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_1 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (3361769569843 / 4000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91145181723 / 4000000000000 : ℝ))
      (E := (cell12486 ⟨1, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (3361769569843 / 4000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91145181723 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_2 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (21002304970201 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284829187709 / 12500000000000 : ℝ))
      (E := (cell12486 ⟨2, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (21002304970201 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284829187709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_3 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (4198711275567 / 5000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278637504673 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨3, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (4198711275567 / 5000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278637504673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_4 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83939256101159 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278641503267 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨4, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83939256101159 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278641503267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_5 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83904311613927 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139322753099 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨5, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83904311613927 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139322753099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_6 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (1310459250211 / 1562500000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278649521949 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨6, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (1310459250211 / 1562500000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278649521949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_7 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83834497263937 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278653500799 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨7, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83834497263937 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278653500799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_8 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41899813664733 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (18229260069 / 800000000000 : ℝ))
      (E := (cell12486 ⟨8, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41899813664733 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (18229260069 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_9 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16752956434903 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278661495147 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨9, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16752956434903 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278661495147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_10 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (5233122610231 / 6250000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455733105157 / 20000000000000 : ℝ))
      (E := (cell12486 ⟨10, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (5233122610231 / 6250000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455733105157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_11 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16739033212361 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278669491663 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨11, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16739033212361 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278669491663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_12 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (2614387344807 / 3125000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113933675787 / 5000000000000 : ℝ))
      (E := (cell12486 ⟨12, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (2614387344807 / 3125000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113933675787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_13 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (20906412161229 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569669372137 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨13, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (20906412161229 / 25000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569669372137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_14 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41795463430213 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (71208796079 / 3125000000000 : ℝ))
      (E := (cell12486 ⟨14, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41795463430213 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (71208796079 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_15 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (2088905741147 / 2500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569671369957 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨15, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (2088905741147 / 2500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569671369957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_16 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41760778483491 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278689510353 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨16, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41760778483491 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278689510353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_17 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (83486908789617 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284836681923 / 12500000000000 : ℝ))
      (E := (cell12486 ⟨17, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (83486908789617 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284836681923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_18 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41726142539921 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278697494829 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨18, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41726142539921 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278697494829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_19 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16683537160779 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91148058369 / 4000000000000 : ℝ))
      (E := (cell12486 ⟨19, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16683537160779 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (91148058369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12487_0 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (84079267992113 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139246972107 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨0, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (84079267992113 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139246972107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_1 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (84044223922881 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278497936557 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨1, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (84044223922881 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278497936557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_2 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (8400920488571 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (227850190697 / 10000000000000 : ℝ))
      (E := (cell12487 ⟨2, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (8400920488571 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (227850190697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_3 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41987105421941 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569626480643 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨3, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41987105421941 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569626480643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_4 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (10492405220109 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139254967277 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨4, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (10492405220109 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139254967277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_5 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (1678085952007 / 2000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (364562223 / 16000000000 : ℝ))
      (E := (cell12487 ⟨5, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (1678085952007 / 2000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (364562223 / 16000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_6 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (3354775133047 / 4000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (142407370277 / 6250000000000 : ℝ))
      (E := (cell12487 ⟨6, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (3354775133047 / 4000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (142407370277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_7 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (20958620975599 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455704383799 / 20000000000000 : ℝ))
      (E := (cell12487 ⟨7, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (20958620975599 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (455704383799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_8 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83799614293253 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278525885339 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨8, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83799614293253 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278525885339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_9 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83764769463171 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139264944557 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨9, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83764769463171 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139264944557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_10 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (20932487344191 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (28481673497 / 1250000000000 : ℝ))
      (E := (cell12487 ⟨10, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (20932487344191 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (28481673497 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_11 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83695153998829 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139268932211 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨11, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83695153998829 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139268932211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_12 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83660383294347 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (71204434627 / 3125000000000 : ℝ))
      (E := (cell12487 ⟨12, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83660383294347 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (71204434627 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_13 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (20906409307121 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569636475303 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨13, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (20906409307121 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569636475303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_14 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41795457883293 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139274954153 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨14, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41795457883293 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139274954153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_15 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41778109437089 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139276938679 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨15, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41778109437089 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139276938679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_16 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83521546516967 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (56963946809 / 2500000000000 : ℝ))
      (E := (cell12487 ⟨16, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83521546516967 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (56963946809 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_17 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41743449330419 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (284820237371 / 12500000000000 : ℝ))
      (E := (cell12487 ⟨17, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41743449330419 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (284820237371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_18 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83452275271849 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139282923089 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨18, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83452275271849 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139282923089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_19 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (83417676316239 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139284946859 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨19, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (83417676316239 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139284946859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12488_0 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (42039626171431 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278362379457 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨0, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (42039626171431 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278362379457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_1 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (21011052150539 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569591595723 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨1, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (21011052150539 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569591595723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_2 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (21002297473261 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139185182593 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨2, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (21002297473261 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139185182593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_3 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83974196178811 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278374335597 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨3, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83974196178811 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278374335597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_4 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83939227422933 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278378361007 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨4, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83939227422933 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278378361007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_5 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (2097607089727 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455676466883 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨5, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (2097607089727 / 2500000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455676466883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_6 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83869364641113 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569596580541 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨6, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83869364641113 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569596580541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_7 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83834470543081 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139195166241 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨7, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83834470543081 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139195166241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_8 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41899800629613 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139197157681 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨8, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41899800629613 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139197157681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_9 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83764756753973 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278398336453 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨9, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83764756753973 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278398336453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_10 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41864968495969 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139201172597 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨10, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41864968495969 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139201172597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_11 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41847570968959 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278406348731 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨11, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41847570968959 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278406348731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_12 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (2614386611153 / 3125000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139205176977 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨12, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (2614386611153 / 3125000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139205176977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_13 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41812812907019 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278414309413 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨13, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41812812907019 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278414309413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_14 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83590904674691 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455683667533 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨14, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83590904674691 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455683667533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_15 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83556208104383 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139211164323 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨15, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83556208104383 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139211164323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_16 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83521536068819 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227842628819 / 10000000000000 : ℝ))
      (E := (cell12488 ⟨16, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83521536068819 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227842628819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_17 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (16697377706777 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139215169127 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨17, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (16697377706777 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139215169127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_18 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (20863066366411 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284804288711 / 12500000000000 : ℝ))
      (E := (cell12488 ⟨18, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (20863066366411 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284804288711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_19 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (83417666830331 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284804790499 / 12500000000000 : ℝ))
      (E := (cell12488 ⟨19, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (83417666830331 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284804790499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12489_0 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (42039618348061 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (71194714609 / 3125000000000 : ℝ))
      (E := (cell12489 ⟨0, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (42039618348061 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (71194714609 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_1 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (84044193283899 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278234882083 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨1, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (84044193283899 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278234882083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_2 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (84009174902807 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139119438161 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨2, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (84009174902807 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139119438161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_3 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (2624193172379 / 3125000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455648571893 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨3, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (2624193172379 / 3125000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455648571893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_4 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41969606543671 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278246840509 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨4, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41969606543671 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278246840509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_5 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83904269580117 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569562707049 / 25000000000000 : ℝ))
      (E := (cell12489 ⟨5, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83904269580117 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569562707049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_6 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83869350958317 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139127415503 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨6, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83869350958317 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139127415503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_7 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (10479307148249 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139129428583 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨7, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (10479307148249 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139129428583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_8 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (10474948528423 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278262856671 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨8, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (10474948528423 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278262856671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_9 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83764744046921 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139133418583 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨9, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83764744046921 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139133418583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_10 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83729924609217 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455654161209 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨10, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83729924609217 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455654161209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_11 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (2615472808721 / 3125000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278274828497 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨11, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (2615472808721 / 3125000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278274828497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_12 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83660359821471 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139139397671 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨12, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83660359821471 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139139397671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_13 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41812807200789 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278282829339 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨13, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41812807200789 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278282829339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_14 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83590893584743 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139143410359 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨14, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83590893584743 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139143410359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_15 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83556197336493 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (71196588553 / 3125000000000 : ℝ))
      (E := (cell12489 ⟨15, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83556197336493 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (71196588553 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_16 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (83521525622537 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278294816009 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨16, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (83521525622537 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278294816009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_17 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (2087171960219 / 2500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278298831427 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨17, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (2087171960219 / 2500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278298831427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_18 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (3338090226449 / 4000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278302827153 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨18, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (3338090226449 / 4000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278302827153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_19 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (8341765734617 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569576702071 / 25000000000000 : ℝ))
      (E := (cell12489 ⟨19, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (8341765734617 / 10000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569576702071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12490_0 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (8407922105189 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284762426039 / 12500000000000 : ℝ))
      (E := (cell12490 ⟨0, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (8407922105189 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284762426039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_1 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (84044177968111 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278103376319 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨1, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (84044177968111 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278103376319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_2 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (84009159914997 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455621476509 / 20000000000000 : ℝ))
      (E := (cell12490 ⟨2, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (84009159914997 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455621476509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_3 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83974166855833 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278111378461 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨3, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83974166855833 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278111378461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_4 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83939198754097 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284764421633 / 12500000000000 : ℝ))
      (E := (cell12490 ⟨4, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83939198754097 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284764421633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_5 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (4195212778673 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139059687547 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨5, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (4195212778673 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139059687547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_6 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83869337277787 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278123393029 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨6, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83869337277787 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278123393029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_7 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83834443831129 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284765922143 / 12500000000000 : ℝ))
      (E := (cell12490 ⟨7, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83834443831129 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284765922143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_8 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (2618736724929 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139065696657 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨8, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (2618736724929 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139065696657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_9 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41882365671007 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455627078251 / 20000000000000 : ℝ))
      (E := (cell12490 ⟨9, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41882365671007 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455627078251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_10 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41864956114301 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278139378359 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨10, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41864956114301 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278139378359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_11 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (20923779455573 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278143361767 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨11, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (20923779455573 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278143361767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_12 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (8366034808807 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (227814734837 / 10000000000000 : ℝ))
      (E := (cell12490 ⟨12, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (8366034808807 / 10000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (227814734837 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_13 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83625602991103 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278151344807 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨13, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83625602991103 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278151344807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_14 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83590882496739 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (71192354921 / 3125000000000 : ℝ))
      (E := (cell12490 ⟨14, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83590882496739 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (71192354921 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_15 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (83556186570509 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278159334369 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨15, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (83556186570509 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278159334369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_16 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (2088037879453 / 2500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569540834873 / 25000000000000 : ℝ))
      (E := (cell12490 ⟨16, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (2088037879453 / 2500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569540834873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_17 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (4174343414273 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139083660153 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨17, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (4174343414273 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139083660153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_18 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (2607882683081 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278171340363 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨18, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (2607882683081 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278171340363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_19 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (20854411965939 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569543836649 / 25000000000000 : ℝ))
      (E := (cell12490 ⟨19, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (20854411965939 / 25000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569543836649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12491_0 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (42039602705083 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277968001929 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨0, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (42039602705083 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277968001929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_1 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (84044162654791 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284746497653 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨1, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (84044162654791 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284746497653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_2 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (42004572464807 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277975999527 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨2, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (42004572464807 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277975999527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_3 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83974152197923 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (455596001661 / 20000000000000 : ℝ))
      (E := (cell12491 ⟨3, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83974152197923 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (455596001661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_4 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83939184423197 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277983958673 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨4, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83939184423197 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277983958673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_5 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83904241569109 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277987975109 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨5, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83904241569109 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2277987975109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_6 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41934661799761 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1138995975153 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨6, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41934661799761 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1138995975153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_7 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83834430478491 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227799595037 / 10000000000000 : ℝ))
      (E := (cell12491 ⟨7, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83834430478491 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227799595037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_8 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83799562170257 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227799998327 / 10000000000000 : ℝ))
      (E := (cell12491 ⟨8, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83799562170257 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227799998327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_9 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83764718639251 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139001970361 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨9, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83764718639251 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139001970361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_10 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83729899850091 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569501986523 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨10, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83729899850091 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569501986523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_11 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (10461888220947 / 12500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (4449242087 / 195312500000 : ℝ))
      (E := (cell12491 ⟨11, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (10461888220947 / 12500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (4449242087 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_12 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41830168178347 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284751994371 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨12, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41830168178347 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284751994371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_13 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (20906397895653 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278019972003 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨13, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (20906397895653 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278019972003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_14 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (2089771785267 / 2500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (91120957917 / 4000000000000 : ℝ))
      (E := (cell12491 ⟨14, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (2089771785267 / 2500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (91120957917 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_15 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83556175806429 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139013973473 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨15, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83556175806429 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139013973473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_16 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (83521504735569 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139015958401 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨16, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (83521504735569 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139015958401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_17 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41743429081993 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142377245079 / 6250000000000 : ℝ))
      (E := (cell12491 ⟨17, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41743429081993 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142377245079 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_18 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16690447211549 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (113901998287 / 5000000000000 : ℝ))
      (E := (cell12491 ⟨18, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16690447211549 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (113901998287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_19 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (5213602398943 / 6250000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142377746183 / 6250000000000 : ℝ))
      (E := (cell12491 ⟨19, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (5213602398943 / 6250000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (142377746183 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12492_0 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (1681583795419 / 2000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (113891832417 / 5000000000000 : ℝ))
      (E := (cell12492 ⟨0, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (1681583795419 / 2000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (113891832417 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_1 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (84044147343937 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227784063899 / 10000000000000 : ℝ))
      (E := (cell12492 ⟨1, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (84044147343937 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227784063899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_2 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (42004564973329 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138922305799 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨2, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (42004564973329 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138922305799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_3 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (13120958991 / 15625000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (7118276979 / 312500000000 : ℝ))
      (E := (cell12492 ⟨3, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (13120958991 / 15625000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (7118276979 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_4 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20984792523661 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455570519467 / 20000000000000 : ℝ))
      (E := (cell12492 ⟨4, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20984792523661 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455570519467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_5 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83904227567063 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569464157061 / 25000000000000 : ℝ))
      (E := (cell12492 ⟨5, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83904227567063 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569464157061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_6 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41934654961761 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277860618697 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨6, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41934654961761 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277860618697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_7 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83834417128077 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138932317399 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨7, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83834417128077 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138932317399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_8 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (8379954914497 / 10000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277868626541 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨8, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (8379954914497 / 10000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277868626541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_9 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83764705938633 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277872601567 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨9, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83764705938633 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277872601567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_10 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83729887473683 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569469156323 / 25000000000000 : ℝ))
      (E := (cell12492 ⟨10, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83729887473683 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569469156323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_11 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20923773428731 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277880588829 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨11, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20923773428731 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277880588829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_12 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41830162313671 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277884615139 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨12, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41830162313671 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277884615139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_13 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (16725116035221 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277888594743 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨13, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (16725116035221 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277888594743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_14 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41795430163283 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138946296039 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨14, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41795430163283 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138946296039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_15 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41778082522127 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284737076661 / 12500000000000 : ℝ))
      (E := (cell12492 ⟨15, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41778082522127 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284737076661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_16 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41760747147441 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138950303053 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨16, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41760747147441 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138950303053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_17 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (83486848044337 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455580915223 / 20000000000000 : ℝ))
      (E := (cell12492 ⟨17, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (83486848044337 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455580915223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_18 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20863056564671 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142369286679 / 6250000000000 : ℝ))
      (E := (cell12492 ⟨18, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20863056564671 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (142369286679 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_19 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41708814452083 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277912585283 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨19, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41708814452083 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2277912585283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12493_0 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (84079174134241 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277705347547 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨0, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (84079174134241 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277705347547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_1 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (1680882640711 / 2000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (142356834351 / 6250000000000 : ℝ))
      (E := (cell12493 ⟨1, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (1680882640711 / 2000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (142356834351 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_2 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (84009114966127 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277713334431 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨2, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (84009114966127 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277713334431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_3 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83974122889261 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138858655623 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨3, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83974122889261 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138858655623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_4 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16787831153687 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138860644527 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨4, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16787831153687 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138860644527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_5 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83904213567321 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277725334501 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨5, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83904213567321 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277725334501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_6 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41934648124893 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455545856469 / 20000000000000 : ℝ))
      (E := (cell12493 ⟨6, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41934648124893 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455545856469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_7 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41917201889943 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (91109332581 / 4000000000000 : ℝ))
      (E := (cell12493 ⟨7, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41917201889943 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (91109332581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_8 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41899768060933 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277737323127 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨8, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41899768060933 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277737323127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_9 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41882346620079 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (142358832237 / 6250000000000 : ℝ))
      (E := (cell12493 ⟨9, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41882346620079 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (142358832237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_10 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (4186493754969 / 5000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284718162489 / 12500000000000 : ℝ))
      (E := (cell12493 ⟨10, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (4186493754969 / 5000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284718162489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_11 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (5230942604021 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277749282623 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨11, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (5230942604021 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277749282623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_12 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83660312900013 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277753270813 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨12, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83660312900013 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277753270813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_13 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (41812784385791 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (28471965889 / 1250000000000 : ℝ))
      (E := (cell12493 ⟨13, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (41812784385791 / 50000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (28471965889 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_14 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16718169848879 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277761289933 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨14, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16718169848879 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277761289933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_15 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83556154283983 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277765275257 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨15, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83556154283983 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277765275257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_16 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83521483856059 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138884645539 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨16, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83521483856059 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138884645539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_17 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (5217927370407 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138886642431 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨17, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (5217927370407 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138886642431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_18 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (2607881764419 / 3125000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138888630973 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨18, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (2607881764419 / 3125000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138888630973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_19 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (83417619426989 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (113889064283 / 5000000000000 : ℝ))
      (E := (cell12493 ⟨19, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (83417619426989 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (113889064283 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12494_0 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (42039579250019 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277574099553 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨0, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (42039579250019 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277574099553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_1 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (21011029182407 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138789027647 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨1, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (21011029182407 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138789027647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_2 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (42004549994011 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569395513089 / 25000000000000 : ℝ))
      (E := (cell12494 ⟨2, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (42004549994011 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569395513089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_3 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (20993527059627 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455517208441 / 20000000000000 : ℝ))
      (E := (cell12494 ⟨3, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (20993527059627 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455517208441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_4 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (8393914144457 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277590033833 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨4, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (8393914144457 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277590033833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_5 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83904199569883 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91103761439 / 4000000000000 : ℝ))
      (E := (cell12494 ⟨5, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83904199569883 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91103761439 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_6 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41934641289157 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277598057109 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨6, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41934641289157 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277598057109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_7 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (130991235053 / 156250000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277602047503 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨7, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (130991235053 / 156250000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277602047503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_8 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41899761550473 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138803007527 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨8, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41899761550473 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138803007527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_9 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41882340271913 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (11388050127 / 500000000000 : ℝ))
      (E := (cell12494 ⟨9, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41882340271913 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (11388050127 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_10 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83729862727179 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (113880701399 / 5000000000000 : ℝ))
      (E := (cell12494 ⟨10, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83729862727179 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (113880701399 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_11 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (8369506961581 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284702253741 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨11, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (8369506961581 / 10000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284702253741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_12 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83660301174707 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277622038133 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨12, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83660301174707 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277622038133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_13 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41812778684521 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138813000569 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨13, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41812778684521 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138813000569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_14 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83590838164167 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138815020747 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨14, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83590838164167 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138815020747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_15 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (5222258970351 / 6250000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277634049133 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨15, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (5222258970351 / 6250000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277634049133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_16 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (835214734191 / 1000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138819014941 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨16, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (835214734191 / 1000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138819014941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_17 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (83486827810511 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138820994659 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨17, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (83486827810511 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138820994659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_18 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (20863051666479 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227764599099 / 10000000000000 : ℝ))
      (E := (cell12494 ⟨18, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (20863051666479 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (227764599099 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_19 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41708804975779 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138825020031 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨19, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41708804975779 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138825020031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12495_0 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (84079142868341 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284680355821 / 12500000000000 : ℝ))
      (E := (cell12495 ⟨0, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (84079142868341 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284680355821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_1 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (21011025356543 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (71170214739 / 3125000000000 : ℝ))
      (E := (cell12495 ⟨1, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (21011025356543 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (71170214739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_2 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (84009085012341 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277450881047 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨2, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (84009085012341 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277450881047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_3 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41987046795069 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138727413079 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨3, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41987046795069 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138727413079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_4 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83939127123049 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277458831669 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨4, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83939127123049 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277458831669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_5 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (20976046393687 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277462848479 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨5, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (20976046393687 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277462848479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_6 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (5241829306819 / 6250000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138733413567 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨6, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (5241829306819 / 6250000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138733413567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_7 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (654956071017 / 781250000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284683854217 / 12500000000000 : ℝ))
      (E := (cell12495 ⟨7, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (654956071017 / 781250000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284683854217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_8 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (2618734690069 / 3125000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (91098992731 / 4000000000000 : ℝ))
      (E := (cell12495 ⟨8, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (2618734690069 / 3125000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (91098992731 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_9 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (20941166962409 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277478846391 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨9, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (20941166962409 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277478846391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_10 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83729850357081 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138741404747 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨10, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83729850357081 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138741404747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_11 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83695057569347 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455497366149 / 20000000000000 : ℝ))
      (E := (cell12495 ⟨11, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83695057569347 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455497366149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_12 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (2614384045357 / 3125000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277490800959 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨12, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (2614384045357 / 3125000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277490800959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_13 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16725109193697 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277494842889 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨13, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16725109193697 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277494842889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_14 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41795413542941 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138749394321 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨14, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41795413542941 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138749394321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_15 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83556132769151 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (28468785233 / 1250000000000 : ℝ))
      (E := (cell12495 ⟨15, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83556132769151 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (28468785233 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_16 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16704292596801 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138753411259 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨16, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16704292596801 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138753411259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_17 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16697363539267 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138755402929 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨17, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16697363539267 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138755402929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_18 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (5215762304513 / 6250000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138757416103 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨18, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (5215762304513 / 6250000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138757416103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_19 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (83417600477871 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455503758051 / 20000000000000 : ℝ))
      (E := (cell12495 ⟨19, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (83417600477871 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455503758051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12496_0 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (84079127239149 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569327926043 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨0, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (84079127239149 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569327926043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_1 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (4202204306259 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455463136611 / 20000000000000 : ℝ))
      (E := (cell12496 ⟨1, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (4202204306259 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455463136611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_2 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (21002267509771 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (8895780097 / 390625000000 : ℝ))
      (E := (cell12496 ⟨2, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (21002267509771 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (8895780097 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_3 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83974078944153 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138661860483 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨3, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83974078944153 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138661860483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_4 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83939112803871 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138663841283 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨4, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83939112803871 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138663841283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_5 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20976042895479 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138665828101 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨5, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20976042895479 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138665828101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_6 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41934627621079 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277335708277 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨6, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41934627621079 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277335708277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_7 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41917181874327 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277339673223 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨7, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41917181874327 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277339673223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_8 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20949874266413 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (35583494919 / 1562500000000 : ℝ))
      (E := (cell12496 ⟨8, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20949874266413 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (35583494919 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_9 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83764655157589 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569336915691 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨9, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83764655157589 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569336915691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_10 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20932459497271 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277351644457 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨10, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20932459497271 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277351644457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_11 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (16739009104989 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (91094227403 / 4000000000000 : ℝ))
      (E := (cell12496 ⟨11, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (16739009104989 / 20000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (91094227403 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_12 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83660277730163 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284669959429 / 12500000000000 : ℝ))
      (E := (cell12496 ⟨12, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83660277730163 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284669959429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_13 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83625534569909 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277363680189 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨13, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83625534569909 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277363680189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_14 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (4179540800477 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277367647613 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨14, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (4179540800477 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277367647613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_15 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83556122014589 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569342910479 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨15, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83556122014589 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569342910479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_16 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20880363137693 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277375668991 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨16, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20880363137693 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277375668991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_17 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (83486807583981 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138689838149 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨17, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (83486807583981 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138689838149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_18 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20863046770071 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138691834587 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨18, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20863046770071 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138691834587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_19 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (10427198875741 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277387652709 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨19, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (10427198875741 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277387652709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12497_0 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (42039555806231 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138590307289 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨0, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (42039555806231 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138590307289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_1 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (21011017706663 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277184605141 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨1, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (21011017706663 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277184605141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_2 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (84009055068251 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569297145387 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨2, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (84009055068251 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569297145387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_3 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (1679481286011 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277192610911 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨3, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (1679481286011 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277192610911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_4 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16787819697407 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91087863461 / 4000000000000 : ℝ))
      (E := (cell12497 ⟨4, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16787819697407 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91087863461 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_5 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41952078795693 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277200574957 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨5, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41952078795693 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277200574957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_6 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83869241577473 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138602292341 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨6, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83869241577473 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138602292341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_7 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41917175204677 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455441713193 / 20000000000000 : ℝ))
      (E := (cell12497 ⟨7, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41917175204677 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455441713193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_8 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41899742025639 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277212584677 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨8, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41899742025639 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277212584677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_9 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83764642467683 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569304147631 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨9, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83764642467683 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569304147631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_10 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83729825623189 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (227722053287 / 10000000000000 : ℝ))
      (E := (cell12497 ⟨10, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83729825623189 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (227722053287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_11 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16739006696521 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277224534873 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨11, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16739006696521 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277224534873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_12 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83660266010923 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138614272707 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨12, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83660266010923 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138614272707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_13 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16725104634663 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569308142783 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨13, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16725104634663 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569308142783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_14 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83590804935139 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277236560291 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨14, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83590804935139 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277236560291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_15 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83556111261929 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569310129741 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨15, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83556111261929 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569310129741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_16 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41760721059701 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138622284649 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨16, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41760721059701 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138622284649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_17 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (1669735949469 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (45544970849 / 2000000000000 : ℝ))
      (E := (cell12497 ⟨17, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (1669735949469 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (45544970849 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_18 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (83452177290143 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138626280053 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨18, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (83452177290143 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138626280053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_19 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (5213598845983 / 6250000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138628255479 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨19, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (5213598845983 / 6250000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138628255479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12498_0 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (84079095988279 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277049519999 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨0, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (84079095988279 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277049519999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_1 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (21011013882647 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277053522283 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨1, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (21011013882647 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277053522283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_2 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (32816031289 / 39062500000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277057511199 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨2, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (32816031289 / 39062500000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277057511199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_3 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83974049659329 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569265373999 / 25000000000000 : ℝ))
      (E := (cell12498 ⟨3, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83974049659329 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569265373999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_4 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41969542086271 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277065543547 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨4, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41969542086271 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277065543547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_5 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41952071801579 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455413897787 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨5, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41952071801579 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455413897787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_6 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83869227915049 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277073514281 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨6, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83869227915049 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277073514281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_7 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (3353373482891 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277077511967 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨7, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (3353373482891 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277077511967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_8 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16759894207817 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569270372471 / 25000000000000 : ℝ))
      (E := (cell12498 ⟨8, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16759894207817 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569270372471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_9 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83764629779917 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277085513671 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨9, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83764629779917 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277085513671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_10 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16745962651879 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455417894947 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨10, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16745962651879 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455417894947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_11 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41847510721163 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277093496233 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨11, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41847510721163 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277093496233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_12 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (10457531786713 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138548734489 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨12, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (10457531786713 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138548734489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_13 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83625511778703 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277101515719 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨13, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83625511778703 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277101515719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_14 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83590793862679 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277105468563 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨14, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83590793862679 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277105468563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_15 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83556100511171 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138554753963 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨15, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83556100511171 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138554753963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_16 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83521431689893 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (7115979579 / 312500000000 : ℝ))
      (E := (cell12498 ⟨16, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83521431689893 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (7115979579 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_17 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (83486787364741 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284639682813 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨17, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (83486787364741 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284639682813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_18 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16690433500357 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569280376251 / 25000000000000 : ℝ))
      (E := (cell12498 ⟨18, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16690433500357 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (569280376251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_19 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (10427196508409 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (227712548147 / 10000000000000 : ℝ))
      (E := (cell12498 ⟨19, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (10427196508409 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (227712548147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12499_0 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (84079080366599 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138459268007 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨0, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (84079080366599 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138459268007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_1 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (42022020118493 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284615311537 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨1, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (42022020118493 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284615311537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_2 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (21002256283463 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284615811723 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨2, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (21002256283463 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284615811723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_3 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (8397403502049 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276930491941 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨3, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (8397403502049 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276930491941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_4 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (8393906986039 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284616811969 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨4, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (8393906986039 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284616811969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_5 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83904129617231 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276938513949 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨5, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83904129617231 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276938513949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_6 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41934607127443 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (91077699883 / 4000000000000 : ℝ))
      (E := (cell12499 ⟨6, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41934607127443 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (91077699883 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_7 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (10479290467177 / 12500000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569236627807 / 25000000000000 : ℝ))
      (E := (cell12499 ⟨7, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (10479290467177 / 12500000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (569236627807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_8 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (5237466126817 / 6250000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276950506393 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨8, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (5237466126817 / 6250000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276950506393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_9 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20941154273573 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276954490207 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨9, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20941154273573 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276954490207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_10 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83729800897701 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276958470053 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨10, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83729800897701 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276958470053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_11 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83695009404107 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284620313889 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨11, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83695009404107 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284620313889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_12 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16732048515701 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138483252097 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨12, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16732048515701 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138483252097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_13 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (8362550038607 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276970455861 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨13, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (8362550038607 / 10000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276970455861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_14 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83590782792161 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276974488661 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨14, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83590782792161 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276974488661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_15 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41778044881157 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138489246261 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨15, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41778044881157 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138489246261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_16 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41760710631123 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142311404579 / 6250000000000 : ℝ))
      (E := (cell12499 ⟨16, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41760710631123 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142311404579 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_17 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41743388628927 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (45539729893 / 2000000000000 : ℝ))
      (E := (cell12499 ⟨17, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41743388628927 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (45539729893 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_18 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83452157715209 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276990445659 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨18, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83452157715209 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276990445659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_19 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (83417562600559 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276994447779 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨19, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (83417562600559 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2276994447779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

end BstLean.Part268
