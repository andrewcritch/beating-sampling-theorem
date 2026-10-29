import BstLean.Part268CellShard5Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12475_40 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (8269671878941 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140118242291 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨40, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (8269671878941 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140118242291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_41 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (2583207669927 / 3125000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280240496563 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨41, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (2583207669927 / 3125000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280240496563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_42 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (8262859579399 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280244477279 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨42, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (8262859579399 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280244477279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_43 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (3303782793141 / 4000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280248485027 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨43, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (3303782793141 / 4000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280248485027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_44 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41280283755777 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (8907236403 / 390625000000 : ℝ))
      (E := (cell12475 ⟨44, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41280283755777 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (8907236403 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_45 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (10315823601689 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140128259999 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨45, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (10315823601689 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140128259999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_46 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (41246316852493 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456052097273 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨46, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (41246316852493 / 50000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456052097273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_47 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82458702156707 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280264475797 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨47, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82458702156707 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280264475797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_48 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82424794139557 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (114013424339 / 5000000000000 : ℝ))
      (E := (cell12475 ⟨48, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82424794139557 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (114013424339 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_49 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82390909624563 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570068129397 / 25000000000000 : ℝ))
      (E := (cell12475 ⟨49, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82390909624563 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (570068129397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_50 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (5147315536431 / 6250000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280276507321 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨50, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (5147315536431 / 6250000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280276507321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_51 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (658585687887 / 800000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280280512739 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨51, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (658585687887 / 800000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280280512739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_52 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82289396804961 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140142236233 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨52, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82289396804961 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140142236233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_53 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82255606011757 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140144250959 / 50000000000000 : ℝ))
      (E := (cell12475 ⟨53, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82255606011757 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (1140144250959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_54 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (8222183857801 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456058496053 / 20000000000000 : ℝ))
      (E := (cell12475 ⟨54, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (8222183857801 / 10000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (456058496053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_55 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82188094475609 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (71259266331 / 3125000000000 : ℝ))
      (E := (cell12475 ⟨55, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82188094475609 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (71259266331 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_56 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (82154373676581 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (57007512689 / 2500000000000 : ℝ))
      (E := (cell12475 ⟨56, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (82154373676581 / 100000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (57007512689 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_57 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (10265084519137 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280304490801 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨57, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (10265084519137 / 12500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280304490801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_58 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (4104350093873 / 5000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280308527841 / 100000000000000 : ℝ))
      (E := (cell12475 ⟨58, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (4104350093873 / 5000000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (2280308527841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12475_59 : CellCertificate 12475 (446542590010877 / 5000000000000000 : ℝ) (841865862197067 / 500000000000000000 : ℝ) (170127683537697 / 5000000000000000 : ℝ)
    (cell12475 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · norm_num [cell12475]
  · have h := gap_lower (n := 12475) (a := (2051333770553 / 2500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228031249657 / 10000000000000 : ℝ))
      (E := (cell12475 ⟨59, by decide⟩).energy) (xi := (170127683537697 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12475 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12475]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12475])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12475) (a := (2051333770553 / 2500000000000 : ℝ)) (b := (33030276611 / 20000000000000 : ℝ)) (q := (228031249657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12475])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12475]

theorem cert12476_40 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82696715916429 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280104305821 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨40, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82696715916429 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280104305821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_41 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16532528575157 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (456021659953 / 20000000000000 : ℝ))
      (E := (cell12476 ⟨41, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16532528575157 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (456021659953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_42 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82628593542783 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140056160961 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨42, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82628593542783 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140056160961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_43 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (2064864197189 / 2500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280116313069 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨43, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (2064864197189 / 2500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280116313069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_44 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82560565880403 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142507520707 / 6250000000000 : ℝ))
      (E := (cell12476 ⟨44, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82560565880403 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (142507520707 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_45 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82526587491747 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280124316949 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨45, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82526587491747 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280124316949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_46 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (4124631634609 / 5000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570032081923 / 25000000000000 : ℝ))
      (E := (cell12476 ⟨46, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (4124631634609 / 5000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570032081923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_47 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41229350726217 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140066151679 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨47, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41229350726217 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140066151679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_48 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82424793743391 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140068150639 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨48, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82424793743391 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140068150639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_49 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82390909536079 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (91205612789 / 4000000000000 : ℝ))
      (E := (cell12476 ⟨49, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82390909536079 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (91205612789 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_50 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82357048801671 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280144356757 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨50, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82357048801671 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280144356757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_51 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16464642302297 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570037087809 / 25000000000000 : ℝ))
      (E := (cell12476 ⟨51, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16464642302297 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (570037087809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_52 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (10286174704623 / 12500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280152359731 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨52, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (10286174704623 / 12500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280152359731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_53 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82255607149771 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280156320633 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨53, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82255607149771 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280156320633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_54 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41110920010797 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228016034919 / 10000000000000 : ℝ))
      (E := (cell12476 ⟨54, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41110920010797 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (228016034919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_55 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82188096224343 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (456032864863 / 20000000000000 : ℝ))
      (E := (cell12476 ⟨55, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82188096224343 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (456032864863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_56 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (41077187865023 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280168360931 / 100000000000000 : ℝ))
      (E := (cell12476 ⟨56, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (41077187865023 / 50000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (2280168360931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_57 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (10265084813859 / 12500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (14251077109 / 625000000000 : ℝ))
      (E := (cell12476 ⟨57, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (10265084813859 / 12500000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (14251077109 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_58 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (82087004539129 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140088184221 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨58, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (82087004539129 / 100000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140088184221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12476_59 : CellCertificate 12476 (178611253803851 / 2000000000000000 : ℝ) (1683596721568117 / 1000000000000000000 : ℝ) (85056849946893 / 2500000000000000 : ℝ)
    (cell12476 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · norm_num [cell12476]
  · have h := gap_lower (n := 12476) (a := (16410670757453 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140090165913 / 50000000000000 : ℝ))
      (E := (cell12476 ⟨59, by decide⟩).energy) (xi := (85056849946893 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12476 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12476]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12476])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12476) (a := (16410670757453 / 20000000000000 : ℝ)) (b := (165137976983 / 100000000000000 : ℝ)) (q := (1140090165913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12476])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12476]

theorem cert12477_40 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41348356522191 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455994436479 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨40, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41348356522191 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455994436479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_41 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82662640314801 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455995243423 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨41, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82662640314801 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (455995243423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_42 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82628591292433 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139990111013 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨42, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82628591292433 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139990111013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_43 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41297282973707 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139992098317 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨43, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41297282973707 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1139992098317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_44 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82560564250031 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569997049761 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨44, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82560564250031 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (569997049761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_45 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20631646542681 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279992228391 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨45, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20631646542681 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279992228391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_46 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82492631680077 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279996224731 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨46, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82492631680077 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2279996224731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_47 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41229350374413 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (456000037339 / 20000000000000 : ℝ))
      (E := (cell12477 ⟨47, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41229350374413 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (456000037339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_48 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (20606198336963 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280004230529 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨48, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (20606198336963 / 25000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280004230529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_49 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16478181889637 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280008236699 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨49, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16478181889637 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280008236699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_50 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41178524510499 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1140006101597 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨50, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41178524510499 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1140006101597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_51 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82323212037609 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280016186773 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨51, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82323212037609 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280016186773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_52 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82289398469483 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1140010122037 / 50000000000000 : ℝ))
      (E := (cell12477 ⟨52, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82289398469483 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (1140010122037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_53 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82255608288223 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280024195497 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨53, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82255608288223 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280024195497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_54 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82221841465579 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280028215271 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨54, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82221841465579 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280028215271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_55 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (256837806167 / 312500000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (570008060347 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨55, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (256837806167 / 312500000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (570008060347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_56 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16430875556767 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280036211537 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨56, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16430875556767 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280036211537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_57 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (16424136173787 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280040240477 / 100000000000000 : ℝ))
      (E := (cell12477 ⟨57, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (16424136173787 / 20000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (2280040240477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_58 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (82087007201049 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (142502762897 / 6250000000000 : ℝ))
      (E := (cell12477 ⟨58, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (82087007201049 / 100000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (142502762897 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12477_59 : CellCertificate 12477 (223256840618573 / 2500000000000000 : ℝ) (1683461740389611 / 1000000000000000000 : ℝ) (68039887436899 / 2000000000000000 : ℝ)
    (cell12477 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · norm_num [cell12477]
  · have h := gap_lower (n := 12477) (a := (41026678376311 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (570012055901 / 25000000000000 : ℝ))
      (E := (cell12477 ⟨59, by decide⟩).energy) (xi := (68039887436899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12477 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12477]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12477])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12477) (a := (41026678376311 / 50000000000000 : ℝ)) (b := (165124573109 / 100000000000000 : ℝ)) (q := (570012055901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12477])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12477]

theorem cert12478_40 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (20674177543317 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279840114307 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨40, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (20674177543317 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279840114307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_41 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (10332829719339 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455968826223 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨41, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (10332829719339 / 12500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455968826223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_42 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41314294521469 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279848118823 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨42, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41314294521469 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279848118823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_43 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (16518912801617 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279852135727 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨43, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (16518912801617 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279852135727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_44 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (2064014065511 / 2500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569964030591 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨44, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (2064014065511 / 2500000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569964030591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_45 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41263292425221 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279860136643 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨45, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41263292425221 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279860136643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_46 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41246315334339 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139932059309 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨46, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41246315334339 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139932059309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_47 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82458700045883 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279868125809 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨47, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82458700045883 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279868125809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_48 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82424792952941 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (71246004897 / 3125000000000 : ℝ))
      (E := (cell12478 ⟨48, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82424792952941 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (71246004897 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_49 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (1029886367011 / 1250000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139938075319 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨49, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (1029886367011 / 1250000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139938075319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_50 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (20589262310219 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569970041139 / 25000000000000 : ℝ))
      (E := (cell12478 ⟨50, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (20589262310219 / 25000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (569970041139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_51 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82323212564247 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279884137321 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨51, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82323212564247 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279884137321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_52 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41144699651229 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279888125499 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨52, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41144699651229 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279888125499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_53 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41127804713557 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279892126511 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨53, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41127804713557 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279892126511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_54 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (16444368581993 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455979227513 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨54, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (16444368581993 / 20000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455979227513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_55 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (821880997229 / 1000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279900155659 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨55, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (821880997229 / 1000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279900155659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_56 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82154379837951 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279904177581 / 100000000000000 : ℝ))
      (E := (cell12478 ⟨56, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82154379837951 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (2279904177581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_57 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82120683227287 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139954070393 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨57, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82120683227287 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139954070393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_58 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (41043504931609 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139956079937 / 50000000000000 : ℝ))
      (E := (cell12478 ⟨58, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (41043504931609 / 50000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (1139956079937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12478_59 : CellCertificate 12478 (111624807548223 / 1250000000000000 : ℝ) (1683326780853409 / 1000000000000000000 : ℝ) (340171479264859 / 10000000000000000 : ℝ)
    (cell12478 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · norm_num [cell12478]
  · have h := gap_lower (n := 12478) (a := (82053359718193 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455983234381 / 20000000000000 : ℝ))
      (E := (cell12478 ⟨59, by decide⟩).energy) (xi := (340171479264859 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12478 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12478]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12478])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12478) (a := (82053359718193 / 100000000000000 : ℝ)) (b := (165111171431 / 100000000000000 : ℝ)) (q := (455983234381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12478])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12478]

theorem cert12479_40 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41348353651543 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569927025389 / 25000000000000 : ℝ))
      (E := (cell12479 ⟨40, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41348353651543 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (569927025389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_41 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20665658798879 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279712100517 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨41, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20665658798879 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279712100517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_42 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82628586794299 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139858064927 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨42, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82628586794299 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139858064927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_43 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82594562069573 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455944026069 / 20000000000000 : ℝ))
      (E := (cell12479 ⟨43, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82594562069573 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455944026069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_44 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82560560991627 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279724101273 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨44, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82560560991627 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279724101273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_45 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82526583530901 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139864050273 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨45, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82526583530901 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139864050273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_46 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82492629657981 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455946425417 / 20000000000000 : ℝ))
      (E := (cell12479 ⟨46, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82492629657981 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (455946425417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_47 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (16491739868721 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279736120699 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨47, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (16491739868721 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279736120699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_48 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (1287887383729 / 1562500000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279740138719 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨48, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (1287887383729 / 1562500000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279740138719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_49 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (20597727318541 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279744120477 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨49, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (20597727318541 / 25000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279744120477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_50 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (16471409892261 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279748122921 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨50, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (16471409892261 / 20000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279748122921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_51 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41161606545699 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139876071947 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨51, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41161606545699 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139876071947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_52 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82289400135909 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139878061009 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨52, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82289400135909 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139878061009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_53 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82255610566443 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (91190404547 / 4000000000000 : ℝ))
      (E := (cell12479 ⟨53, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82255610566443 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (91190404547 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_54 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82221844354751 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (227976411607 / 10000000000000 : ℝ))
      (E := (cell12479 ⟨54, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82221844354751 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (227976411607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_55 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82188101472723 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279768126203 / 100000000000000 : ℝ))
      (E := (cell12479 ⟨55, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82188101472723 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (2279768126203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_56 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82154381892391 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (113988607043 / 5000000000000 : ℝ))
      (E := (cell12479 ⟨56, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82154381892391 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (113988607043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_57 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (41060342792963 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (113988807831 / 5000000000000 : ℝ))
      (E := (cell12479 ⟨57, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (41060342792963 / 50000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (113988807831 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_58 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82087012525639 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139890084927 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨58, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82087012525639 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139890084927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12479_59 : CellCertificate 12479 (892969562752653 / 10000000000000000 : ℝ) (1683191842954307 / 1000000000000000000 : ℝ) (340143526027359 / 10000000000000000 : ℝ)
    (cell12479 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · norm_num [cell12479]
  · have h := gap_lower (n := 12479) (a := (82053362683977 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139892088363 / 50000000000000 : ℝ))
      (E := (cell12479 ⟨59, by decide⟩).energy) (xi := (340143526027359 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12479 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12479]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12479])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12479) (a := (82053362683977 / 100000000000000 : ℝ)) (b := (165097771951 / 100000000000000 : ℝ)) (q := (1139892088363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12479])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12479]

theorem cert12480_40 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82696704433837 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142473509009 / 6250000000000 : ℝ))
      (E := (cell12480 ⟨40, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82696704433837 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (142473509009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_41 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (16532526527443 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279580184069 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨41, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (16532526527443 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279580184069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_42 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (20657146136629 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139792068789 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨42, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (20657146136629 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139792068789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_43 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82594560131879 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227958818049 / 10000000000000 : ℝ))
      (E := (cell12480 ⟨43, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82594560131879 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227958818049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_44 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41280279681797 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569898033943 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨44, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41280279681797 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569898033943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_45 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82526582212101 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455919235789 / 20000000000000 : ℝ))
      (E := (cell12480 ⟨45, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82526582212101 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (455919235789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_46 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (20623157161997 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279600191267 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨46, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (20623157161997 / 25000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279600191267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_47 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (10307337330249 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279604171367 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨47, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (10307337330249 / 12500000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279604171367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_48 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82424792164999 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279608176573 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨48, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82424792164999 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279608176573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_49 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41195454594019 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139806073109 / 50000000000000 : ℝ))
      (E := (cell12480 ⟨49, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41195454594019 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (1139806073109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_50 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (16471409936457 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279616196211 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨50, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (16471409936457 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279616196211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_51 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82323213619063 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227962014751 / 10000000000000 : ℝ))
      (E := (cell12480 ⟨51, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82323213619063 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (227962014751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_52 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (16457880193967 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569906043657 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨52, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (16457880193967 / 20000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569906043657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_53 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (8225561170621 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279628156991 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨53, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (8225561170621 / 10000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279628156991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_54 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82221845799937 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279632150791 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨54, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82221845799937 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279632150791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_55 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82188103222909 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279636153023 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨55, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82188103222909 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279636153023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_56 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82154383947157 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569910040119 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨56, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82154383947157 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569910040119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_57 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82120687944853 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (4452430019 / 195312500000 : ℝ))
      (E := (cell12480 ⟨57, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82120687944853 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (4452430019 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_58 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (82087015188309 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569912044287 / 25000000000000 : ℝ))
      (E := (cell12480 ⟨58, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (82087015188309 / 100000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (569912044287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12480_59 : CellCertificate 12480 (892940669573819 / 10000000000000000 : ℝ) (1683056926687101 / 1000000000000000000 : ℝ) (340115577470691 / 10000000000000000 : ℝ)
    (cell12480 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · norm_num [cell12480]
  · have h := gap_lower (n := 12480) (a := (41026682824987 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279652178899 / 100000000000000 : ℝ))
      (E := (cell12480 ⟨59, by decide⟩).energy) (xi := (340115577470691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12480 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12480]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12480])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12480) (a := (41026682824987 / 50000000000000 : ℝ)) (b := (165084374667 / 100000000000000 : ℝ)) (q := (2279652178899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12480])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12480]

theorem cert12481_40 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82696701565519 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139722121037 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨40, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82696701565519 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139722121037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_41 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82662630079807 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279448264277 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨41, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82662630079807 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279448264277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_42 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20657145574897 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139726129771 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨42, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20657145574897 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139726129771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_43 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41297279097501 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (227945622737 / 10000000000000 : ℝ))
      (E := (cell12481 ⟨43, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41297279097501 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (227945622737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_44 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (4128027886817 / 5000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279460225863 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨44, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (4128027886817 / 5000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279460225863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_45 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82526580894041 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139732127079 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨45, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82526580894041 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139732127079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_46 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82492627638697 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279468252301 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨46, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82492627638697 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279468252301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_47 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20614674485261 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284934034727 / 12500000000000 : ℝ))
      (E := (cell12481 ⟨47, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20614674485261 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (284934034727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_48 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (1287887371437 / 1562500000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279476270271 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨48, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (1287887371437 / 1562500000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279476270271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_49 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (32956363641 / 40000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139740113933 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨49, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (32956363641 / 40000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139740113933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_50 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82357049903817 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569871066627 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨50, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82357049903817 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569871066627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_51 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (2058080353681 / 2500000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279488266141 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨51, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (2058080353681 / 2500000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279488266141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_52 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82289401804237 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (227949228333 / 10000000000000 : ℝ))
      (E := (cell12481 ⟨52, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82289401804237 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (227949228333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_53 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (41127806423207 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139748128231 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨53, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (41127806423207 / 50000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139748128231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_54 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82221847245523 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279500241727 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨54, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82221847245523 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279500241727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_55 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82188104973457 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139752118061 / 50000000000000 : ℝ))
      (E := (cell12481 ⟨55, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82188104973457 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (1139752118061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_56 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82154386002247 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (142469268471 / 6250000000000 : ℝ))
      (E := (cell12481 ⟨56, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82154386002247 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (142469268471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_57 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (20530172576017 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279512298363 / 100000000000000 : ℝ))
      (E := (cell12481 ⟨57, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (20530172576017 / 25000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (2279512298363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_58 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (8208701785123 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455903260011 / 20000000000000 : ℝ))
      (E := (cell12481 ⟨58, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (8208701785123 / 10000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (455903260011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12481_59 : CellCertificate 12481 (446455890424101 / 5000000000000000 : ℝ) (168292203204659 / 100000000000000000 : ℝ) (170043816796777 / 5000000000000000 : ℝ)
    (cell12481 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · norm_num [cell12481]
  · have h := gap_lower (n := 12481) (a := (82053368616183 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569880074193 / 25000000000000 : ℝ))
      (E := (cell12481 ⟨59, by decide⟩).energy) (xi := (170043816796777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12481 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12481]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12481])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12481) (a := (82053368616183 / 100000000000000 : ℝ)) (b := (165070979577 / 100000000000000 : ℝ)) (q := (569880074193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12481])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12481]

theorem cert12482_40 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82696698698133 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455862479069 / 20000000000000 : ℝ))
      (E := (cell12482 ⟨40, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82696698698133 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455862479069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_41 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (20665656880823 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279316399889 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨41, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (20665656880823 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279316399889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_42 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16525716010703 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279320378199 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨42, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16525716010703 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279320378199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_43 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41297278129471 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139662194287 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨43, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41297278129471 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139662194287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_44 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (10320069513733 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139664185773 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨44, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (10320069513733 / 12500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139664185773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_45 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82526579576723 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139666192511 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨45, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82526579576723 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139666192511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_46 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82492626630109 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279336369051 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨46, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82492626630109 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279336369051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_47 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (2061467431019 / 2500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279340381153 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨47, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (2061467431019 / 2500000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279340381153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_48 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (20606197844891 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227934441981 / 10000000000000 : ℝ))
      (E := (cell12482 ⟨48, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (20606197844891 / 25000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (227934441981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_49 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (1647818180351 / 2000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569837106089 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨49, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (1647818180351 / 2000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569837106089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_50 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82357050125899 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569838098193 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨50, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82357050125899 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569838098193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_51 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82323214675931 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284919547727 / 12500000000000 : ℝ))
      (E := (cell12482 ⟨51, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82323214675931 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284919547727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_52 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82289402639113 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455872077823 / 20000000000000 : ℝ))
      (E := (cell12482 ⟨52, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82289402639113 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455872077823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_53 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (5140975874191 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455872882417 / 20000000000000 : ℝ))
      (E := (cell12482 ⟨53, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (5140975874191 / 6250000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (455872882417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_54 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82221848691509 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279368388879 / 100000000000000 : ℝ))
      (E := (cell12482 ⟨54, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82221848691509 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (2279368388879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_55 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82188106724367 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139686187749 / 50000000000000 : ℝ))
      (E := (cell12482 ⟨55, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82188106724367 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (1139686187749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_56 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (41077194028831 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284922053479 / 12500000000000 : ℝ))
      (E := (cell12482 ⟨56, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (41077194028831 / 50000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (284922053479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_57 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (82120692663569 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569845106069 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨57, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (82120692663569 / 100000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569845106069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_58 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (102608775643 / 125000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569846105069 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨58, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (102608775643 / 125000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569846105069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12482_59 : CellCertificate 12482 (35715315862989 / 400000000000000 : ℝ) (67311486361103 / 40000000000000000 : ℝ) (340059694394643 / 10000000000000000 : ℝ)
    (cell12482 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · norm_num [cell12482]
  · have h := gap_lower (n := 12482) (a := (16410674316521 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569847102999 / 25000000000000 : ℝ))
      (E := (cell12482 ⟨59, by decide⟩).energy) (xi := (340059694394643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12482 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12482]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12482])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12482) (a := (16410674316521 / 20000000000000 : ℝ)) (b := (165057586683 / 100000000000000 : ℝ)) (q := (569847102999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12482])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12482]

theorem cert12483_40 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82696695831679 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279180603959 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨40, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82696695831679 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279180603959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_41 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82662624967671 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455836918181 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨41, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82662624967671 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455836918181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_42 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82628577808297 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569797138081 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨42, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82628577808297 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569797138081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_43 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41297277161849 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227919260531 / 10000000000000 : ℝ))
      (E := (cell12483 ⟨43, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41297277161849 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227919260531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_44 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41280277242083 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (284899571603 / 12500000000000 : ℝ))
      (E := (cell12483 ⟨44, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41280277242083 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (284899571603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_45 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (5157911141259 / 6250000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455840114309 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨45, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (5157911141259 / 6250000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455840114309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_46 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41246312811111 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569801150097 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨46, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41246312811111 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569801150097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_47 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82458696541141 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139604299581 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨47, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82458696541141 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139604299581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_48 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (16484958197557 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (56980314157 / 2500000000000 : ℝ))
      (E := (cell12483 ⟨48, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (16484958197557 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (56980314157 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_49 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82390908933189 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569804139719 / 25000000000000 : ℝ))
      (E := (cell12483 ⟨49, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82390908933189 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (569804139719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_50 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82357050348531 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455844115001 / 20000000000000 : ℝ))
      (E := (cell12483 ⟨50, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82357050348531 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (455844115001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_51 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41161607602567 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139612306253 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨51, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41161607602567 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139612306253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_52 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (16457880694893 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279228610001 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨52, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (16457880694893 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279228610001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_53 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (16451123025627 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279232564833 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨53, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (16451123025627 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279232564833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_54 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (16444370027579 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (284904574031 / 12500000000000 : ℝ))
      (E := (cell12483 ⟨54, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (16444370027579 / 20000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (284904574031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_55 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82188108475639 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139620285577 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨55, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82188108475639 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139620285577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_56 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41077195056701 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227924461647 / 10000000000000 : ℝ))
      (E := (cell12483 ⟨56, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41077195056701 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227924461647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_57 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (41060347511679 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227924860659 / 10000000000000 : ℝ))
      (E := (cell12483 ⟨57, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (41060347511679 / 50000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (227924860659 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_58 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (4104351158891 / 5000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139626298481 / 50000000000000 : ℝ))
      (E := (cell12483 ⟨58, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (4104351158891 / 5000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (1139626298481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12483_59 : CellCertificate 12483 (892854016752309 / 10000000000000000 : ℝ) (841326153812429 / 500000000000000000 : ℝ) (170015879936329 / 5000000000000000 : ℝ)
    (cell12483 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · norm_num [cell12483]
  · have h := gap_lower (n := 12483) (a := (82053374549239 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279256583747 / 100000000000000 : ℝ))
      (E := (cell12483 ⟨59, by decide⟩).energy) (xi := (170015879936329 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12483 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12483]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12483])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12483) (a := (82053374549239 / 100000000000000 : ℝ)) (b := (165044195983 / 100000000000000 : ℝ)) (q := (2279256583747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12483])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12483]

theorem cert12484_40 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16539338593231 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279048809191 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨40, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16539338593231 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279048809191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_41 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41331311206471 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279052837329 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨41, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41331311206471 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279052837329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_42 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82628575563933 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279056840693 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨42, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82628575563933 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279056840693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_43 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (8259455238927 / 10000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139530409391 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨43, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (8259455238927 / 10000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139530409391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_44 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82560552859247 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (8902596991 / 390625000000 : ℝ))
      (E := (cell12484 ⟨44, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82560552859247 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (8902596991 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_45 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16505315388861 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569767203431 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨45, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16505315388861 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569767203431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_46 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41246312307519 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279072828577 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨46, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41246312307519 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279072828577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_47 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (16491739168437 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279076814063 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨47, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (16491739168437 / 20000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279076814063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_48 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82424790596633 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569770206877 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨48, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82424790596633 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569770206877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_49 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (10298863606177 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279084808241 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨49, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (10298863606177 / 12500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279084808241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_50 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41178525285857 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139544406603 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨50, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41178525285857 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139544406603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_51 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (1646464314697 / 2000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569773210061 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨51, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (1646464314697 / 2000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569773210061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_52 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (20572351077573 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569774206993 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨52, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (20572351077573 / 25000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569774206993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_53 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82255616269651 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2225684407 / 97656250000 : ℝ))
      (E := (cell12484 ⟨53, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82255616269651 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2225684407 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_54 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (2055546289617 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569776212959 / 25000000000000 : ℝ))
      (E := (cell12484 ⟨54, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (2055546289617 / 2500000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (569776212959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_55 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41094055113637 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279108823089 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨55, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41094055113637 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279108823089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_56 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (82154392169467 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279112861449 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨56, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (82154392169467 / 100000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279112861449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_57 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41060348691717 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279116845309 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨57, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41060348691717 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279116845309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_58 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (8208702584149 / 10000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139560415057 / 50000000000000 : ℝ))
      (E := (cell12484 ⟨58, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (8208702584149 / 10000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (1139560415057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12484_59 : CellCertificate 12484 (892825141379877 / 10000000000000000 : ℝ) (841258738916621 / 500000000000000000 : ℝ) (170001915013149 / 5000000000000000 : ℝ)
    (cell12484 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · norm_num [cell12484]
  · have h := gap_lower (n := 12484) (a := (41026688758043 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279124871199 / 100000000000000 : ℝ))
      (E := (cell12484 ⟨59, by decide⟩).energy) (xi := (170001915013149 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12484 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12484]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12484])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12484) (a := (41026688758043 / 50000000000000 : ℝ)) (b := (165030807477 / 100000000000000 : ℝ)) (q := (2279124871199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12484])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12484]

theorem cert12485_40 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41348345050781 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139458564247 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨40, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41348345050781 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139458564247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_41 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41331309929553 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (56973028479 / 2500000000000 : ℝ))
      (E := (cell12485 ⟨41, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41331309929553 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (56973028479 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_42 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82628573320423 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278925125759 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨42, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82628573320423 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278925125759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_43 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82594550455659 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278929087787 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨43, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82594550455659 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278929087787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_44 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16512110247021 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (142433317709 / 6250000000000 : ℝ))
      (E := (cell12485 ⟨44, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16512110247021 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (142433317709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_45 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82526575629207 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139468555781 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨45, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82526575629207 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139468555781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_46 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (20623155902139 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278941112487 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨46, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (20623155902139 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278941112487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_47 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82458695143893 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569736271187 / 25000000000000 : ℝ))
      (E := (cell12485 ⟨47, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82458695143893 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569736271187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_48 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82424790206107 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278949085667 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨48, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82424790206107 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278949085667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_49 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82390908766231 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455790622703 / 20000000000000 : ℝ))
      (E := (cell12485 ⟨49, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82390908766231 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (455790622703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_50 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82357050795447 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278957107379 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨50, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82357050795447 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278957107379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_51 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (41161608132539 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139480562007 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨51, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (41161608132539 / 50000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139480562007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_52 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82289405146593 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278965102039 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨52, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82289405146593 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278965102039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_53 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (20563904352901 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569742274457 / 25000000000000 : ℝ))
      (E := (cell12485 ⟨53, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (20563904352901 / 25000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (569742274457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_54 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (10277731628983 / 12500000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278973108587 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨54, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (10277731628983 / 12500000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278973108587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_55 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (8218811197927 / 10000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278977131307 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨55, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (8218811197927 / 10000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278977131307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_56 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16430878845171 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278981103671 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨56, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16430878845171 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278981103671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_57 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82120699743797 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278985140433 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨57, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82120699743797 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278985140433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_58 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (82087028505409 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139494559867 / 50000000000000 : ℝ))
      (E := (cell12485 ⟨58, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (82087028505409 / 100000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (1139494559867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12485_59 : CellCertificate 12485 (17855925409127 / 200000000000000 : ℝ) (1682382669647533 / 1000000000000000000 : ℝ) (169987952427131 / 5000000000000000 : ℝ)
    (cell12485 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · norm_num [cell12485]
  · have h := gap_lower (n := 12485) (a := (16410676096629 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278993156007 / 100000000000000 : ℝ))
      (E := (cell12485 ⟨59, by decide⟩).energy) (xi := (169987952427131 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12485 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12485]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12485])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12485) (a := (16410676096629 / 20000000000000 : ℝ)) (b := (41254355291 / 25000000000000 : ℝ)) (q := (2278993156007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12485])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12485]

theorem cert12486_40 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (826966872379 / 1000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (35606022569 / 1562500000000 : ℝ))
      (E := (cell12486 ⟨40, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (826966872379 / 1000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (35606022569 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_41 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41331308653081 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278789437651 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨41, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41331308653081 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278789437651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_42 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10328571384721 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284849183287 / 12500000000000 : ℝ))
      (E := (cell12486 ⟨42, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10328571384721 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (284849183287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_43 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82594548522863 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278797471123 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨43, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82594548522863 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278797471123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_44 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82560549611741 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278801451409 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨44, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82560549611741 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278801451409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_45 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82526574314847 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113940273253 / 5000000000000 : ℝ))
      (E := (cell12486 ⟨45, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82526574314847 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113940273253 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_46 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41246311301387 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (56970236303 / 2500000000000 : ℝ))
      (E := (cell12486 ⟨46, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41246311301387 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (56970236303 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_47 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10307336805783 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569703367527 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨47, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10307336805783 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569703367527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_48 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41212394908103 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569704364647 / 25000000000000 : ℝ))
      (E := (cell12486 ⟨48, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41212394908103 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (569704364647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_49 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41195454341817 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278821474697 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨49, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41195454341817 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278821474697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_50 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82357051019729 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278825457523 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨50, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82357051019729 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278825457523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_51 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41161608397909 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139414731909 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨51, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41161608397909 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139414731909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_52 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10286175747921 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (227883349121 / 10000000000000 : ℝ))
      (E := (cell12486 ⟨52, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10286175747921 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (227883349121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_53 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41127809276997 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278837478079 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨53, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41127809276997 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278837478079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_54 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10277731809931 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139420740307 / 50000000000000 : ℝ))
      (E := (cell12486 ⟨54, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10277731809931 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (1139420740307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_55 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82188113731627 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278845495807 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨55, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82188113731627 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278845495807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_56 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (10269299535321 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278849461337 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨56, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (10269299535321 / 12500000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278849461337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_57 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (82120702104447 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278853491963 / 100000000000000 : ℝ))
      (E := (cell12486 ⟨57, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (82120702104447 / 100000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (2278853491963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_58 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (41043515584789 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113942873291 / 5000000000000 : ℝ))
      (E := (cell12486 ⟨58, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (41043515584789 / 50000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (113942873291 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12486_59 : CellCertificate 12486 (892767403980651 / 10000000000000000 : ℝ) (841123941531269 / 500000000000000000 : ℝ) (339947984355249 / 10000000000000000 : ℝ)
    (cell12486 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · norm_num [cell12486]
  · have h := gap_lower (n := 12486) (a := (16410676690083 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455772299469 / 20000000000000 : ℝ))
      (E := (cell12486 ⟨59, by decide⟩).energy) (xi := (339947984355249 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12486 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12486]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12486])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12486) (a := (16410676690083 / 20000000000000 : ℝ)) (b := (41251009261 / 25000000000000 : ℝ)) (q := (455772299469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12486])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12486]

theorem cert12487_40 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (646067846681 / 781250000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278653815687 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨40, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (646067846681 / 781250000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278653815687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_41 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82662614754109 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278657850303 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨41, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82662614754109 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278657850303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_42 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41314284417983 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278661862307 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨42, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41314284417983 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278661862307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_43 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82594546590883 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139332925599 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨43, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82594546590883 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139332925599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_44 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16512109597831 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569667454063 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨44, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16512109597831 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569667454063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_45 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82526573001227 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278673874219 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨45, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82526573001227 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278673874219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_46 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41246310798847 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278677847477 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨46, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41246310798847 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278677847477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_47 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82458693749299 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278681852363 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨47, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82458693749299 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278681852363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_48 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (8242478942693 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569671457111 / 25000000000000 : ℝ))
      (E := (cell12487 ⟨48, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (8242478942693 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (569671457111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_49 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (10298863575203 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278689832853 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨49, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (10298863575203 / 12500000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278689832853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_50 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41178525622281 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (56967346591 / 2500000000000 : ℝ))
      (E := (cell12487 ⟨50, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41178525622281 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (56967346591 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_51 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (8232321732707 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139348929829 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨51, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (8232321732707 / 10000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139348929829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_52 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41144703410309 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278701877471 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨52, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41144703410309 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278701877471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_53 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (4112780984841 / 5000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139352927729 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨53, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (4112780984841 / 5000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139352927729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_54 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82221855927431 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278709849807 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨54, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82221855927431 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278709849807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_55 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82188115484347 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (227871385751 / 10000000000000 : ℝ))
      (E := (cell12487 ⟨55, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82188115484347 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (227871385751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_56 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (16430879667921 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278717875351 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨56, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (16430879667921 / 20000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278717875351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_57 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (82120704465383 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139360920387 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨57, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (82120704465383 / 100000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139360920387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_58 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (20521758458499 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278725868377 / 100000000000000 : ℝ))
      (E := (cell12487 ⟨58, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (20521758458499 / 25000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (2278725868377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12487_59 : CellCertificate 12487 (111592317743963 / 1250000000000000 : ℝ) (336422623614613 / 200000000000000000 : ℝ) (169960034263981 / 5000000000000000 : ℝ)
    (cell12487 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · norm_num [cell12487]
  · have h := gap_lower (n := 12487) (a := (41026693208949 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139364947607 / 50000000000000 : ℝ))
      (E := (cell12487 ⟨59, by decide⟩).energy) (xi := (169960034263981 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12487 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12487]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12487])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12487) (a := (41026693208949 / 50000000000000 : ℝ)) (b := (32998131023 / 20000000000000 : ℝ)) (q := (1139364947607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12487])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12487]

theorem cert12488_40 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41348340756683 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284815287629 / 12500000000000 : ℝ))
      (E := (cell12488 ⟨40, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41348340756683 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284815287629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_41 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82662612202949 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455705251923 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨41, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82662612202949 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455705251923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_42 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82628566595017 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278530313793 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨42, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82628566595017 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278530313793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_43 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82594544659717 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227853428681 / 10000000000000 : ℝ))
      (E := (cell12488 ⟨43, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82594544659717 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227853428681 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_44 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (16512109273469 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569634573879 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨44, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (16512109273469 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569634573879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_45 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41263285844173 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455708456039 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨45, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41263285844173 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455708456039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_46 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (20623155148329 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569636574639 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨46, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (20623155148329 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569636574639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_47 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82458693052997 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455710058081 / 20000000000000 : ℝ))
      (E := (cell12488 ⟨47, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82458693052997 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (455710058081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_48 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82424789038279 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284819289133 / 12500000000000 : ℝ))
      (E := (cell12488 ⟨48, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82424789038279 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (284819289133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_49 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82390908520201 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139279152929 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨49, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82390908520201 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139279152929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_50 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82357051469943 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227856226677 / 10000000000000 : ℝ))
      (E := (cell12488 ⟨50, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82357051469943 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (227856226677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_51 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82323217858833 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139283155767 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨51, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82323217858833 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139283155767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_52 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41144703829171 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278570319829 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨52, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41144703829171 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278570319829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_53 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82255620840083 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569643572249 / 25000000000000 : ℝ))
      (E := (cell12488 ⟨53, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82255620840083 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (569643572249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_54 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (20555464343953 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139289137611 / 50000000000000 : ℝ))
      (E := (cell12488 ⟨54, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (20555464343953 / 25000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (1139289137611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_55 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82188117237427 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278582275499 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨55, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82188117237427 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278582275499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_56 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (41077200198483 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278586286607 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨56, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (41077200198483 / 50000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278586286607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_57 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (16424141365321 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278590305121 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨57, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (16424141365321 / 20000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278590305121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_58 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82087036498663 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278594327403 / 100000000000000 : ℝ))
      (E := (cell12488 ⟨58, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82087036498663 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (2278594327403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12488_59 : CellCertificate 12488 (892709684368433 / 10000000000000000 : ℝ) (420494593668481 / 250000000000000000 : ℝ) (169946078685551 / 5000000000000000 : ℝ)
    (cell12488 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · norm_num [cell12488]
  · have h := gap_lower (n := 12488) (a := (82053389385593 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (56964957261 / 2500000000000 : ℝ))
      (E := (cell12488 ⟨59, by decide⟩).energy) (xi := (169946078685551 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12488 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12488]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12488])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12488) (a := (82053389385593 / 100000000000000 : ℝ)) (b := (82488637689 / 50000000000000 : ℝ)) (q := (56964957261 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12488])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12488]

theorem cert12489_40 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41348339326247 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278390783 / 100000000000 : ℝ))
      (E := (cell12489 ⟨40, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41348339326247 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278390783 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_41 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (2066565241317 / 2500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278394783089 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨41, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (2066565241317 / 2500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278394783089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_42 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41314282177461 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139199380989 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨42, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41314282177461 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139199380989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_43 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82594542729367 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278402777959 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨43, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82594542729367 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278402777959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_44 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (10320068093289 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278406771559 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨44, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (10320068093289 / 12500000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278406771559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_45 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (20631642594051 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139205400339 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨45, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (20631642594051 / 25000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139205400339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_46 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82492619589637 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278414805363 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨46, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82492619589637 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278414805363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_47 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82458692357357 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455683756847 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨47, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82458692357357 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455683756847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_48 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41212394325127 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139211397309 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨48, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41212394325127 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139211397309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_49 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (16478181687873 / 20000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139213387919 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨49, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (16478181687873 / 20000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139213387919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_50 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41178525847937 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569607696209 / 25000000000000 : ℝ))
      (E := (cell12489 ⟨50, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41178525847937 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569607696209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_51 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82323218391109 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278434760461 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨51, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82323218391109 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278434760461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_52 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (4114470424827 / 5000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139219409143 / 50000000000000 : ℝ))
      (E := (cell12489 ⟨52, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (4114470424827 / 5000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1139219409143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_53 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41127810991891 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455688555739 / 20000000000000 : ℝ))
      (E := (cell12489 ⟨53, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41127810991891 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (455688555739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_54 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82221858824593 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569611703979 / 25000000000000 : ℝ))
      (E := (cell12489 ⟨54, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82221858824593 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (569611703979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_55 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82188118990869 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278450808851 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨55, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82188118990869 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278450808851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_56 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (1643088049093 / 2000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278454813313 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨56, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (1643088049093 / 2000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278454813313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_57 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (41060354594057 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (18227670607 / 800000000000 : ℝ))
      (E := (cell12489 ⟨57, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (41060354594057 / 50000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (18227670607 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_58 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82087039163579 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1822770227 / 80000000000 : ℝ))
      (E := (cell12489 ⟨58, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82087039163579 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (1822770227 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12489_59 : CellCertificate 12489 (2789627597593 / 31250000000000 : ℝ) (1681843652859929 / 1000000000000000000 : ℝ) (339864250883369 / 10000000000000000 : ℝ)
    (cell12489 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · norm_num [cell12489]
  · have h := gap_lower (n := 12489) (a := (82053392353499 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278466801373 / 100000000000000 : ℝ))
      (E := (cell12489 ⟨59, by decide⟩).energy) (xi := (339864250883369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12489 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12489]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12489])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12489) (a := (82053392353499 / 100000000000000 : ℝ)) (b := (20620487229 / 12500000000000 : ℝ)) (q := (2278466801373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12489])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12489]

theorem cert12490_40 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82696675792551 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (889945047 / 39062500000 : ℝ))
      (E := (cell12490 ⟨40, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82696675792551 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (889945047 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_41 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41331303551651 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278263303227 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨41, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41331303551651 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278263303227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_42 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (516428513223 / 625000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139133662207 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨42, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (516428513223 / 625000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139133662207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_43 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (10324317599979 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278271324647 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨43, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (10324317599979 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278271324647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_44 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (10320067890757 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278275303203 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨44, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (10320067890757 / 12500000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278275303203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_45 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (103158211331 / 125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139139658991 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨45, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (103158211331 / 125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139139658991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_46 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (4124630929333 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278283309027 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨46, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (4124630929333 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278283309027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_47 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (4122934583119 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278287333853 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨47, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (4122934583119 / 5000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278287333853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_48 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82424788262853 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284786416503 / 12500000000000 : ℝ))
      (E := (cell12490 ⟨48, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82424788262853 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (284786416503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_49 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82390908359117 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278295301731 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨49, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82390908359117 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278295301731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_50 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41178525961177 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569574824979 / 25000000000000 : ℝ))
      (E := (cell12490 ⟨50, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41178525961177 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569574824979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_51 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (16464643784779 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569575831103 / 25000000000000 : ℝ))
      (E := (cell12490 ⟨51, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (16464643784779 / 20000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (569575831103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_52 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82289409335211 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455661462767 / 20000000000000 : ℝ))
      (E := (cell12490 ⟨52, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82289409335211 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455661462767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_53 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82255623127917 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139155662279 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨53, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82255623127917 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139155662279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_54 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82221860273771 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (113915767689 / 5000000000000 : ℝ))
      (E := (cell12490 ⟨54, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82221860273771 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (113915767689 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_55 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (2568378773271 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278319339411 / 100000000000000 : ℝ))
      (E := (cell12490 ⟨55, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (2568378773271 / 3125000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (2278319339411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_56 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (41077202256329 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455664667453 / 20000000000000 : ℝ))
      (E := (cell12490 ⟨56, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (41077202256329 / 50000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (455664667453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_57 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82120711549909 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139163671957 / 50000000000000 : ℝ))
      (E := (cell12490 ⟨57, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82120711549909 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (1139163671957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_58 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (82087041828743 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (56958283893 / 2500000000000 : ℝ))
      (E := (cell12490 ⟨58, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (82087041828743 / 100000000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (56958283893 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12490_59 : CellCertificate 12490 (892651982534611 / 10000000000000000 : ℝ) (420427238156473 / 250000000000000000 : ℝ) (84959087265867 / 2500000000000000 : ℝ)
    (cell12490 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · norm_num [cell12490]
  · have h := gap_lower (n := 12490) (a := (5128337207601 / 6250000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (56958384221 / 2500000000000 : ℝ))
      (E := (cell12490 ⟨59, by decide⟩).energy) (xi := (84959087265867 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12490 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12490]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12490])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12490) (a := (5128337207601 / 6250000000000 : ℝ)) (b := (41237630619 / 25000000000000 : ℝ)) (q := (56958384221 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12490])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12490]

theorem cert12491_40 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41348336466769 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227812791299 / 10000000000000 : ℝ))
      (E := (cell12491 ⟨40, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41348336466769 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227812791299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_41 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16532520910963 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227813193753 / 10000000000000 : ℝ))
      (E := (cell12491 ⟨41, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16532520910963 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (227813193753 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_42 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (8262855987729 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284766992791 / 12500000000000 : ℝ))
      (E := (cell12491 ⟨42, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (8262855987729 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (284766992791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_43 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82594538871111 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569534981719 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨43, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82594538871111 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569534981719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_44 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (5160033844161 / 6250000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (45562877809 / 2000000000000 : ℝ))
      (E := (cell12491 ⟨44, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (5160033844161 / 6250000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (45562877809 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_45 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16505313550827 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278147890949 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨45, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16505313550827 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278147890949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_46 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41246308792191 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278151927287 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨46, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41246308792191 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278151927287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_47 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41229345484033 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139077969631 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨47, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41229345484033 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139077969631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_48 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82424787876077 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139079962641 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨48, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82424787876077 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139079962641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_49 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (41195454139727 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139081971239 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨49, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (41195454139727 / 50000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139081971239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_50 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82357052149383 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139083964967 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨50, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82357052149383 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139083964967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_51 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82323219457193 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139085972201 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨51, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82323219457193 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139085972201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_52 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (20572352543589 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139087962247 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨52, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (20572352543589 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139087962247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_53 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (10281953034061 / 12500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278179926583 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨53, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (10281953034061 / 12500000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278179926583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_54 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (20555465430837 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569545986967 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨54, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (20555465430837 / 25000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569545986967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_55 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16437624499767 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139093963129 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨55, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16437624499767 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139093963129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_56 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82154406570989 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139095958783 / 50000000000000 : ℝ))
      (E := (cell12491 ⟨56, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82154406570989 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (1139095958783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_57 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (8212071391199 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278195918363 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨57, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (8212071391199 / 10000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278195918363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_58 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (82087044494157 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278199925011 / 100000000000000 : ℝ))
      (E := (cell12491 ⟨58, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (82087044494157 / 100000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (2278199925011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12491_59 : CellCertificate 12491 (892623138281909 / 10000000000000000 : ℝ) (1681574273966629 / 1000000000000000000 : ℝ) (169904225955051 / 5000000000000000 : ℝ)
    (cell12491 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · norm_num [cell12491]
  · have h := gap_lower (n := 12491) (a := (16410679657989 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569550983417 / 25000000000000 : ℝ))
      (E := (cell12491 ⟨59, by decide⟩).energy) (xi := (169904225955051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12491 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12491]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12491])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12491) (a := (16410679657989 / 20000000000000 : ℝ)) (b := (16493714931 / 10000000000000 : ℝ)) (q := (569550983417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12491])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12491]

theorem cert12492_40 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82696670075453 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138998280507 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨40, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82696670075453 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1138998280507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_41 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41331301003609 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278000568499 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨41, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41331301003609 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278000568499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_42 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (10328569704969 / 12500000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139002278473 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨42, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (10328569704969 / 12500000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139002278473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_43 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20648634235801 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455601716929 / 20000000000000 : ℝ))
      (E := (cell12492 ⟨43, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20648634235801 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455601716929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_44 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82560539887873 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (22780125333 / 1000000000000 : ℝ))
      (E := (cell12492 ⟨44, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82560539887873 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (22780125333 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_45 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82526566444207 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278016578429 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨45, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82526566444207 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278016578429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_46 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (16498523316561 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284752567801 / 12500000000000 : ℝ))
      (E := (cell12492 ⟨46, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (16498523316561 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (284752567801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_47 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82458690274413 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227802454157 / 10000000000000 : ℝ))
      (E := (cell12492 ⟨47, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82458690274413 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (227802454157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_48 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20606196872481 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139014287197 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨48, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20606196872481 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139014287197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_49 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82390908200379 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278032580201 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨49, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82390908200379 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278032580201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_50 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82357052376961 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278036556969 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨50, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82357052376961 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278036556969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_51 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41161609995501 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139020280723 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨51, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41161609995501 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139020280723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_52 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41144705506987 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455608918251 / 20000000000000 : ℝ))
      (E := (cell12492 ⟨52, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41144705506987 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (455608918251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_53 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (16451125083499 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569512146193 / 25000000000000 : ℝ))
      (E := (cell12492 ⟨53, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (16451125083499 / 20000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (569512146193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_54 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82221863173323 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278052598183 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨54, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82221863173323 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278052598183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_55 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82188124253359 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139028284697 / 50000000000000 : ℝ))
      (E := (cell12492 ⟨55, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82188124253359 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (1139028284697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_56 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (20538602157411 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278060554217 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨56, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (20538602157411 / 25000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278060554217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_57 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (82120716274357 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (91122581969 / 4000000000000 : ℝ))
      (E := (cell12492 ⟨57, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (82120716274357 / 100000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (91122581969 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_58 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41043523579909 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278068609929 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨58, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41043523579909 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278068609929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12492_59 : CellCertificate 12492 (892594298470581 / 10000000000000000 : ℝ) (1681439616876957 / 1000000000000000000 : ℝ) (169890279710987 / 5000000000000000 : ℝ)
    (cell12492 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · norm_num [cell12492]
  · have h := gap_lower (n := 12492) (a := (41026700629243 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278072555031 / 100000000000000 : ℝ))
      (E := (cell12492 ⟨59, by decide⟩).energy) (xi := (169890279710987 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12492 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12492]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12492])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12492) (a := (41026700629243 / 50000000000000 : ℝ)) (b := (164923778333 / 100000000000000 : ℝ)) (q := (2278072555031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12492])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12492]

theorem cert12493_40 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82696667218297 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284733158049 / 12500000000000 : ℝ))
      (E := (cell12493 ⟨40, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82696667218297 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284733158049 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_41 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (2583206233141 / 3125000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569467313721 / 25000000000000 : ℝ))
      (E := (cell12493 ⟨41, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (2583206233141 / 3125000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569467313721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_42 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82628555403067 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277873227043 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨42, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82628555403067 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277873227043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_43 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (5162158438507 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138938619579 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨43, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (5162158438507 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138938619579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_44 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16512107653989 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455576246351 / 20000000000000 : ℝ))
      (E := (cell12493 ⟨44, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16512107653989 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455576246351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_45 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82526565135017 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277885262731 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨45, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82526565135017 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277885262731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_46 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (10311576947741 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (18223114177 / 800000000000 : ℝ))
      (E := (cell12493 ⟨46, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (10311576947741 / 12500000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (18223114177 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_47 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82458689581423 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138946629281 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨47, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82458689581423 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138946629281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_48 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (20606196776099 / 25000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (3559214499 / 156250000000 : ℝ))
      (E := (cell12493 ⟨48, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (20606196776099 / 25000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (3559214499 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_49 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82390908121889 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277901273841 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨49, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82390908121889 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277901273841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_50 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82357052605087 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138952619991 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨50, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82357052605087 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138952619991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_51 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82323220525321 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569477308633 / 25000000000000 : ℝ))
      (E := (cell12493 ⟨51, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82323220525321 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569477308633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_52 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (16457882370813 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (227791325511 / 10000000000000 : ℝ))
      (E := (cell12493 ⟨52, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (16457882370813 / 20000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (227791325511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_53 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82255626562937 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138958620047 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨53, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82255626562937 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138958620047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_54 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (5138866538981 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569480311417 / 25000000000000 : ℝ))
      (E := (cell12493 ⟨54, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (5138866538981 / 6250000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (569480311417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_55 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (20547031502061 / 25000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138962634409 / 50000000000000 : ℝ))
      (E := (cell12493 ⟨55, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (20547031502061 / 25000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (1138962634409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_56 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82154410688621 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (113896462361 / 5000000000000 : ℝ))
      (E := (cell12493 ⟨56, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82154410688621 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (113896462361 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_57 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82120718637009 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277933295627 / 100000000000000 : ℝ))
      (E := (cell12493 ⟨57, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82120718637009 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (2277933295627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_58 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82087049825729 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284742161521 / 12500000000000 : ℝ))
      (E := (cell12493 ⟨58, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82087049825729 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (284742161521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12493_59 : CellCertificate 12493 (17851309261991 / 200000000000000 : ℝ) (336260996270339 / 200000000000000000 : ℝ) (339752671597789 / 10000000000000000 : ℝ)
    (cell12493 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · norm_num [cell12493]
  · have h := gap_lower (n := 12493) (a := (82053404227237 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455588258421 / 20000000000000 : ℝ))
      (E := (cell12493 ⟨59, by decide⟩).energy) (xi := (339752671597789 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12493 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12493]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12493])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12493) (a := (82053404227237 / 100000000000000 : ℝ)) (b := (32982081909 / 20000000000000 : ℝ)) (q := (455588258421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12493])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12493]

theorem cert12494_40 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82696664362069 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277733964399 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨40, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82696664362069 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277733964399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_41 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (10332824614337 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (142358624793 / 6250000000000 : ℝ))
      (E := (cell12494 ⟨41, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (10332824614337 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (142358624793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_42 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41314276583617 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569435502849 / 25000000000000 : ℝ))
      (E := (cell12494 ⟨42, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41314276583617 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569435502849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_43 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (10324316636229 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455549201603 / 20000000000000 : ℝ))
      (E := (cell12494 ⟨43, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (10324316636229 / 12500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (455549201603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_44 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82560536652793 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284718748227 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨44, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82560536652793 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284718748227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_45 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (16505312765313 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138877001351 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨45, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (16505312765313 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138877001351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_46 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (329970458327 / 400000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569439499677 / 25000000000000 : ℝ))
      (E := (cell12494 ⟨46, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (329970458327 / 400000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (569439499677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_47 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41229344444547 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284720246557 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨47, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41229344444547 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284720246557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_48 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (20606196679873 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277765981267 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨48, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (20606196679873 / 25000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277765981267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_49 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41195454021993 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277770023399 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨49, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41195454021993 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277770023399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_50 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82357052833761 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277773978977 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨50, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82357052833761 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277773978977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_51 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82323221060151 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138889011323 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨51, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82323221060151 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138889011323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_52 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82289412694629 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277781975071 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨52, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82289412694629 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277781975071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_53 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (16451125541763 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284723251327 / 12500000000000 : ℝ))
      (E := (cell12494 ⟨53, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (16451125541763 / 20000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (284723251327 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_54 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82221866074467 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277790008439 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨54, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82221866074467 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277790008439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_55 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82188127763489 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138897012267 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨55, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82188127763489 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138897012267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_56 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (41077206373961 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91111919863 / 4000000000000 : ℝ))
      (E := (cell12494 ⟨56, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (41077206373961 / 50000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (91111919863 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_57 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82120720999947 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277802039317 / 100000000000000 : ℝ))
      (E := (cell12494 ⟨57, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82120720999947 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (2277802039317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_58 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (82087052491887 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138903015443 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨58, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (82087052491887 / 100000000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138903015443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12494_59 : CellCertificate 12494 (892536632167743 / 10000000000000000 : ℝ) (840585183692831 / 500000000000000000 : ℝ) (84931197109063 / 2500000000000000 : ℝ)
    (cell12494 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · norm_num [cell12494]
  · have h := gap_lower (n := 12494) (a := (410267035981 / 500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138905013271 / 50000000000000 : ℝ))
      (E := (cell12494 ⟨59, by decide⟩).energy) (xi := (84931197109063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12494 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12494]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12494])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12494) (a := (410267035981 / 500000000000 : ℝ)) (b := (322064537 / 195312500000 : ℝ)) (q := (1138905013271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12494])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12494]

theorem cert12495_40 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82696661506769 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277602778489 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨40, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82696661506769 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277602778489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_41 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82662594369769 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277606793911 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨41, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82662594369769 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277606793911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_42 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (20657137733063 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284701349057 / 12500000000000 : ℝ))
      (E := (cell12495 ⟨42, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (20657137733063 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (284701349057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_43 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82594531164367 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (142350923351 / 6250000000000 : ℝ))
      (E := (cell12495 ⟨43, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82594531164367 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (142350923351 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_44 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (161251044993 / 195312500000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455523759097 / 20000000000000 : ℝ))
      (E := (cell12495 ⟨44, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (161251044993 / 195312500000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (455523759097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_45 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82526562518851 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277622798341 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨45, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82526562518851 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277622798341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_46 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82492613582271 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277626781021 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨46, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82492613582271 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277626781021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_47 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41229344098713 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569407700259 / 25000000000000 : ℝ))
      (E := (cell12495 ⟨47, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41229344098713 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569407700259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_48 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82424786335211 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138817398973 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨48, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82424786335211 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138817398973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_49 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (20597726991667 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138819384969 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨49, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (20597726991667 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138819384969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_50 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (10294631632873 / 12500000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277642773951 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨50, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (10294631632873 / 12500000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277642773951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_51 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82323221595491 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138823403909 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨51, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82323221595491 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138823403909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_52 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41144706767833 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138825405073 / 50000000000000 : ℝ))
      (E := (cell12495 ⟨52, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41144706767833 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (1138825405073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_53 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82255628855127 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277654778273 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨53, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82255628855127 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277654778273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_54 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (20555466881409 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277658827439 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨54, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (20555466881409 / 25000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277658827439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_55 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (41094064759547 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277662777461 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨55, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (41094064759547 / 50000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277662777461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_56 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (16430882961509 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569416700571 / 25000000000000 : ℝ))
      (E := (cell12495 ⟨56, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (16430882961509 / 20000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (569416700571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_57 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82120723363171 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277670780293 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨57, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82120723363171 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277670780293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_58 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82087055158293 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277674826081 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨58, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82087055158293 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277674826081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12495_59 : CellCertificate 12495 (446253902837043 / 5000000000000000 : ℝ) (1681035774973681 / 1000000000000000000 : ℝ) (33969690993607 / 1000000000000000 : ℝ)
    (cell12495 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · norm_num [cell12495]
  · have h := gap_lower (n := 12495) (a := (82053410165373 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277678817519 / 100000000000000 : ℝ))
      (E := (cell12495 ⟨59, by decide⟩).energy) (xi := (33969690993607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12495 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12495]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12495])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12495) (a := (82053410165373 / 100000000000000 : ℝ)) (b := (164883678531 / 100000000000000 : ℝ)) (q := (2277678817519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12495])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12495]

theorem cert12496_40 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82696658652397 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (35585494499 / 1562500000000 : ℝ))
      (E := (cell12496 ⟨40, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82696658652397 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (35585494499 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_41 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20665647956433 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138737823277 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨41, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20665647956433 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138737823277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_42 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82628548698121 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277479628999 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨42, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82628548698121 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277479628999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_43 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41297264619857 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138741826781 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨43, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41297264619857 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138741826781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_44 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41280266710407 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (113874380097 / 5000000000000 : ℝ))
      (E := (cell12496 ⟨44, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41280266710407 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (113874380097 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_45 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82526561211873 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569372912413 / 25000000000000 : ℝ))
      (E := (cell12496 ⟨45, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82526561211873 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (569372912413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_46 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20623153145873 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277495619067 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨46, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20623153145873 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277495619067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_47 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (4122934375321 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (56937490663 / 2500000000000 : ℝ))
      (E := (cell12496 ⟨47, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (4122934375321 / 5000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (56937490663 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_48 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41212392975777 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138751805783 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨48, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41212392975777 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138751805783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_49 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (5149431743121 / 6250000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455501526267 / 20000000000000 : ℝ))
      (E := (cell12496 ⟨49, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (5149431743121 / 6250000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455501526267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_50 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41178526646377 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277511624909 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨50, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41178526646377 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277511624909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_51 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41161611065671 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277515649033 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨51, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41161611065671 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277515649033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_52 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (10286176797147 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277519642317 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨52, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (10286176797147 / 12500000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277519642317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_53 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (131609008003 / 160000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277523661131 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨53, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (131609008003 / 160000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277523661131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_54 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (41110934488601 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277527643613 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨54, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (41110934488601 / 50000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277527643613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_55 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82188131275059 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (7117286393 / 312500000000 : ℝ))
      (E := (cell12496 ⟨55, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82188131275059 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (7117286393 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_56 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (8215441686749 / 10000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277535664347 / 100000000000000 : ℝ))
      (E := (cell12496 ⟨56, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (8215441686749 / 10000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (2277535664347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_57 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82120725726679 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138769818407 / 50000000000000 : ℝ))
      (E := (cell12496 ⟨57, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82120725726679 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (1138769818407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_58 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (20521764456237 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284692959719 / 12500000000000 : ℝ))
      (E := (cell12496 ⟨58, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (20521764456237 / 25000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (284692959719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12496_59 : CellCertificate 12496 (178495796723501 / 2000000000000000 : ℝ) (105056325256911 / 62500000000000000 : ℝ) (84917259023987 / 2500000000000000 : ℝ)
    (cell12496 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · norm_num [cell12496]
  · have h := gap_lower (n := 12496) (a := (82053413134757 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455509533007 / 20000000000000 : ℝ))
      (E := (cell12496 ⟨59, by decide⟩).energy) (xi := (84917259023987 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12496 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12496]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12496])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12496) (a := (82053413134757 / 100000000000000 : ℝ)) (b := (32974063261 / 20000000000000 : ℝ)) (q := (455509533007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12496])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12496]

theorem cert12497_40 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (10337081974869 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455468102803 / 20000000000000 : ℝ))
      (E := (cell12497 ⟨40, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (10337081974869 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455468102803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_41 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16532517856517 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138672247933 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨41, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16532517856517 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138672247933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_42 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41314273232421 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91093940841 / 4000000000000 : ℝ))
      (E := (cell12497 ⟨42, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41314273232421 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91093940841 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_43 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (660756218527 / 800000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455470506051 / 20000000000000 : ℝ))
      (E := (cell12497 ⟨43, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (660756218527 / 800000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (455470506051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_44 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82560531805987 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91094260913 / 4000000000000 : ℝ))
      (E := (cell12497 ⟨44, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82560531805987 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (91094260913 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_45 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (2578954997051 / 3125000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569340124447 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨45, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (2578954997051 / 3125000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569340124447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_46 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (20623152896353 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138682256423 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨46, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (20623152896353 / 25000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138682256423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_47 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (3298347472643 / 4000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138684253899 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨47, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (3298347472643 / 4000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138684253899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_48 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (2060619639213 / 2500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277372539961 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨48, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (2060619639213 / 2500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277372539961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_49 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82390907813789 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277376548653 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨49, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82390907813789 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277376548653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_50 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (643414480649 / 781250000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277380531849 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨50, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (643414480649 / 781250000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277380531849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_51 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (41161611333851 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138692273147 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨51, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (41161611333851 / 50000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138692273147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_52 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82289415219157 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569347132649 / 25000000000000 : ℝ))
      (E := (cell12497 ⟨52, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82289415219157 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (569347132649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_53 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82255631149057 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (18219140329 / 800000000000 : ℝ))
      (E := (cell12497 ⟨53, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82255631149057 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (18219140329 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_54 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (16444374085833 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138698258009 / 50000000000000 : ℝ))
      (E := (cell12497 ⟨54, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (16444374085833 / 20000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (1138698258009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_55 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (10273516628923 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277400511271 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨55, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (10273516628923 / 12500000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277400511271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_56 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82154418927759 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (113870226183 / 5000000000000 : ℝ))
      (E := (cell12497 ⟨56, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82154418927759 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (113870226183 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_57 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82120728090473 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (9109634199 / 400000000000 : ℝ))
      (E := (cell12497 ⟨57, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82120728090473 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (9109634199 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_58 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (1641741209837 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277412526751 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨58, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (1641741209837 / 2000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277412526751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12497_59 : CellCertificate 12497 (446225082998463 / 5000000000000000 : ℝ) (420191663697793 / 250000000000000000 : ℝ) (339641166914593 / 10000000000000000 : ℝ)
    (cell12497 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · norm_num [cell12497]
  · have h := gap_lower (n := 12497) (a := (82053416104351 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277416569091 / 100000000000000 : ℝ))
      (E := (cell12497 ⟨59, by decide⟩).energy) (xi := (339641166914593 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12497 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12497]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12497])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12497) (a := (82053416104351 / 100000000000000 : ℝ)) (b := (82428478133 / 50000000000000 : ℝ)) (q := (2277416569091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12497])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12497]

theorem cert12498_40 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41348326473217 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138604717727 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨40, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41348326473217 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138604717727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_41 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41331293370163 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277213459353 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨41, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41331293370163 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277213459353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_42 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82628544232413 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277217468537 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨42, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82628544232413 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277217468537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_43 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (5162157837053 / 6250000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277221462497 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨43, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (5162157837053 / 6250000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277221462497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_44 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (16512106038387 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (4554450881 / 200000000000 : ℝ))
      (E := (cell12498 ⟨44, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (16512106038387 / 20000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (4554450881 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_45 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (1289477478127 / 1562500000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277229460443 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨45, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (1289477478127 / 1562500000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277229460443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_46 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (8249261058803 / 10000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138616731181 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨46, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (8249261058803 / 10000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138616731181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_47 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82458686126391 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (18217899559 / 800000000000 : ℝ))
      (E := (cell12498 ⟨47, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82458686126391 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (18217899559 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_48 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (20606196296527 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277241465301 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨48, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (20606196296527 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277241465301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_49 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82390907738227 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455449092591 / 20000000000000 : ℝ))
      (E := (cell12498 ⟨49, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82390907738227 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (455449092591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_50 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82357053753937 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277249435811 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨50, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82357053753937 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277249435811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_51 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82323223204573 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138626720307 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨51, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82323223204573 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138626720307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_52 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82289416061611 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284657184373 / 12500000000000 : ℝ))
      (E := (cell12498 ⟨52, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82289416061611 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (284657184373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_53 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (41127816148337 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (227726147729 / 10000000000000 : ℝ))
      (E := (cell12498 ⟨53, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (41127816148337 / 50000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (227726147729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_54 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (3288874875261 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (142329090291 / 6250000000000 : ℝ))
      (E := (cell12498 ⟨54, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (3288874875261 / 4000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (142329090291 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_55 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82188134788069 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138634746079 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨55, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82188134788069 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138634746079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_56 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82154420988349 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138636749217 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨56, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82154420988349 / 100000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138636749217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_57 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (10265091306819 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138638729989 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨57, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (10265091306819 / 12500000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138638729989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_58 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (82087063159 / 100000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277281491381 / 100000000000000 : ℝ))
      (E := (cell12498 ⟨58, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (82087063159 / 100000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (2277281491381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12498_59 : CellCertificate 12498 (446210676405639 / 5000000000000000 : ℝ) (336126425402059 / 200000000000000000 : ℝ) (169806651195357 / 5000000000000000 : ℝ)
    (cell12498 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · norm_num [cell12498]
  · have h := gap_lower (n := 12498) (a := (20513354768539 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138642735257 / 50000000000000 : ℝ))
      (E := (cell12498 ⟨59, by decide⟩).energy) (xi := (169806651195357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12498 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12498]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12498])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12498) (a := (20513354768539 / 25000000000000 : ℝ)) (b := (41210899603 / 25000000000000 : ℝ)) (q := (1138642735257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12498])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12498]

theorem cert12499_40 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20674162523711 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277078470981 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨40, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20674162523711 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277078470981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_41 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (20665646049739 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284635302439 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨41, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (20665646049739 / 25000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284635302439 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_42 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16525708400167 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142317904471 / 6250000000000 : ℝ))
      (E := (cell12499 ⟨42, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16525708400167 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (142317904471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_43 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41297261735317 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277090450287 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨43, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41297261735317 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277090450287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_44 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82560528578657 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277094472607 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨44, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82560528578657 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277094472607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_45 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82526557295361 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138549209963 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨45, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82526557295361 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138549209963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_46 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82492609591347 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138551233807 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨46, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82492609591347 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138551233807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_47 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82458685437367 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284638304719 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨47, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82458685437367 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284638304719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_48 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (515154905027 / 625000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277110446501 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨48, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (515154905027 / 625000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277110446501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_49 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82390907663251 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277114433179 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨49, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82390907663251 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277114433179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_50 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (1647141079707 / 2000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277118454721 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨50, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (1647141079707 / 2000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277118454721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_51 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (160787546371 / 195312500000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (227712244997 / 10000000000000 : ℝ))
      (E := (cell12499 ⟨51, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (160787546371 / 195312500000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (227712244997 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_52 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82289416904537 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277126475481 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨52, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82289416904537 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277126475481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_53 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41127816722363 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138565234813 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨53, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41127816722363 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138565234813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_54 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82221873334283 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284641811073 / 12500000000000 : ℝ))
      (E := (cell12499 ⟨54, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82221873334283 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (284641811073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_55 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82188136545113 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277138470261 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨55, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82188136545113 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277138470261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_56 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41077211524631 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138571235231 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨56, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41077211524631 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138571235231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_57 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (16424146563783 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138573242877 / 50000000000000 : ℝ))
      (E := (cell12499 ⟨57, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (16424146563783 / 20000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (1138573242877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_58 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (41043532913199 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277150453341 / 100000000000000 : ℝ))
      (E := (cell12499 ⟨58, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (41043532913199 / 50000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (2277150453341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

theorem cert12499_59 : CellCertificate 12499 (446196272029743 / 5000000000000000 : ℝ) (67219904830511 / 40000000000000000 : ℝ) (339585442523019 / 10000000000000000 : ℝ)
    (cell12499 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · norm_num [cell12499]
  · have h := gap_lower (n := 12499) (a := (82053422044171 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (455430897531 / 20000000000000 : ℝ))
      (E := (cell12499 ⟨59, by decide⟩).energy) (xi := (339585442523019 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12499 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12499]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12499])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12499) (a := (82053422044171 / 100000000000000 : ℝ)) (b := (164830242743 / 100000000000000 : ℝ)) (q := (455430897531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12499])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12499]

end BstLean.Part268
