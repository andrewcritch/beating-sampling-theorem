import BstLean.Part268CellShard34Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13200_0 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (84068712678317 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193590848263 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨0, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (84068712678317 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193590848263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_1 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (42016912237593 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193594840519 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨1, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (42016912237593 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193594840519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_2 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16799792216889 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193598897381 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨2, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16799792216889 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193598897381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_3 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83964122469861 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096801455719 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨3, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83964122469861 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096801455719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_4 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16785861719079 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137100430671 / 6250000000000 : ℝ))
      (E := (cell13200 ⟨4, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16785861719079 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137100430671 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_5 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41947259712597 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096805450521 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨5, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41947259712597 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096805450521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_6 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83859754923597 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (54840373749 / 2500000000000 : ℝ))
      (E := (cell13200 ⟨6, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83859754923597 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (54840373749 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_7 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41912507527563 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096809464401 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨7, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41912507527563 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096809464401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_8 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (8379029978449 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193622960619 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨8, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (8379029978449 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193622960619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_9 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83755609076583 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193626994193 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨9, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83755609076583 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193626994193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_10 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (523255893103 / 625000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193630977963 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨10, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (523255893103 / 625000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193630977963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_11 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41843150604721 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193635034369 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨11, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41843150604721 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193635034369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_12 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41825841990453 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (54840976331 / 2500000000000 : ℝ))
      (E := (cell13200 ⟨12, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41825841990453 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (54840976331 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_13 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83617091176491 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548410760073 / 25000000000000 : ℝ))
      (E := (cell13200 ⟨13, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83617091176491 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548410760073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_14 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16716504552399 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193647059183 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨14, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16716504552399 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193647059183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_15 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (2610874334481 / 3125000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096825528501 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨15, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (2610874334481 / 3125000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096825528501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_16 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83513458966833 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096827548483 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨16, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83513458966833 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096827548483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_17 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83478963518643 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (17137961919 / 781250000000 : ℝ))
      (E := (cell13200 ⟨17, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83478963518643 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (17137961919 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_18 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83444492325323 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193663147501 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨18, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83444492325323 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193663147501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_19 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (10426255669193 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096833583417 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨19, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (10426255669193 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096833583417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13201_0 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (2627146833623 / 3125000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193480833371 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨0, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (2627146833623 / 3125000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193480833371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_1 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (42016905239511 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096742440133 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨1, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (42016905239511 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096742440133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_2 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83998947094491 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548372219013 / 25000000000000 : ℝ))
      (E := (cell13201 ⟨2, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83998947094491 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548372219013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_3 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (2623878390191 / 3125000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193492886961 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨3, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (2623878390191 / 3125000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193492886961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_4 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (16785858923569 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193496921109 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨4, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (16785858923569 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193496921109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_5 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83894505453839 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193500928383 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨5, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83894505453839 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193500928383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_6 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (8385974095843 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096752487159 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨6, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (8385974095843 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096752487159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_7 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83825001096141 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137094309389 / 6250000000000 : ℝ))
      (E := (cell13201 ⟨7, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83825001096141 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137094309389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_8 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41895142915841 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137094561197 / 6250000000000 : ℝ))
      (E := (cell13201 ⟨8, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41895142915841 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137094561197 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_9 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83755595129947 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193517009883 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨9, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83755595129947 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193517009883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_10 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83720928956011 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193520990857 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨10, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83720928956011 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193520990857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_11 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83686287275133 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096762522257 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨11, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83686287275133 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096762522257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_12 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (5228229378297 / 6250000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193529060683 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨12, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (5228229378297 / 6250000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193529060683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_13 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10452134656811 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193533045079 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨13, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10452134656811 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193533045079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_14 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10447813605767 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096768530681 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨14, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10447813605767 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096768530681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_15 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10443495599209 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193541114829 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨15, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10443495599209 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193541114829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_16 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83513445063247 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548386273517 / 25000000000000 : ℝ))
      (E := (cell13201 ⟨16, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83513445063247 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548386273517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_17 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41739474810593 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438709824053 / 20000000000000 : ℝ))
      (E := (cell13201 ⟨17, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41739474810593 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438709824053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_18 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83444478433989 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1071070869 / 48828125000 : ℝ))
      (E := (cell13201 ⟨18, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83444478433989 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1071070869 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_19 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10426253933541 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219355715667 / 10000000000000 : ℝ))
      (E := (cell13201 ⟨19, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10426253933541 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219355715667 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13202_0 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (525429279223 / 625000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096685436081 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨0, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (525429279223 / 625000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096685436081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_1 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (84033796484981 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193374915839 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨1, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (84033796484981 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193374915839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_2 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83998933106659 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438675781691 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨2, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83998933106659 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438675781691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_3 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20991023626121 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (27417286453 / 1250000000000 : ℝ))
      (E := (cell13202 ⟨3, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20991023626121 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (27417286453 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_4 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (5245580040151 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193386947311 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨4, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (5245580040151 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193386947311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_5 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41947245742301 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193390951557 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨5, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41947245742301 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193390951557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_6 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (4192986349769 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193394994509 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨6, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (4192986349769 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193394994509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_7 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41912493569637 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (4386798051 / 200000000000 : ℝ))
      (E := (cell13202 ⟨7, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41912493569637 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (4386798051 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_8 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83790271880991 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096701496759 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨8, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83790271880991 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096701496759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_9 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83755581185427 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193407021407 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨9, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83755581185427 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193407021407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_10 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (10465114377207 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096705528839 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨10, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (10465114377207 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096705528839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_11 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41843136671469 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438683010099 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨11, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41843136671469 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438683010099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_12 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (10456457015839 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096709531981 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨12, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (10456457015839 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096709531981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_13 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20904265833649 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193423103867 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨13, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20904265833649 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193423103867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_14 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20895623733097 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438685423513 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨14, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20895623733097 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438685423513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_15 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83547950886063 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548357777571 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨15, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83547950886063 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548357777571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_16 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (8351343116177 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193435145243 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨16, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (8351343116177 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193435145243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_17 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83478935725837 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438687833799 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨17, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83478935725837 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438687833799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_18 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41722232272381 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438688637209 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨18, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41722232272381 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438688637209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_19 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41705008792609 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548361800163 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨19, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41705008792609 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548361800163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13203_0 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (42034335338773 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096630482319 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨0, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (42034335338773 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096630482319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_1 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (42016891246531 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193264947239 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨1, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (42016891246531 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193264947239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_2 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83998919120949 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219326899459 / 10000000000000 : ℝ))
      (E := (cell13203 ⟨2, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83998919120949 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219326899459 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_3 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83964080524977 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548318249819 / 25000000000000 : ℝ))
      (E := (cell13203 ⟨3, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83964080524977 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548318249819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_4 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41964633334553 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (68539907103 / 3125000000000 : ℝ))
      (E := (cell13203 ⟨4, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41964633334553 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (68539907103 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_5 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (20973619379371 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (438656205707 / 20000000000000 : ℝ))
      (E := (cell13203 ⟨5, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (20973619379371 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (438656205707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_6 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83859713034449 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219328501053 / 10000000000000 : ℝ))
      (E := (cell13203 ⟨6, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83859713034449 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219328501053 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_7 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83824973184523 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193289038587 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨7, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83824973184523 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193289038587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_8 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (654611390097 / 781250000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096646530881 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨8, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (654611390097 / 781250000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096646530881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_9 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83755567243021 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096648543417 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨9, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83755567243021 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096648543417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_10 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16744180216283 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193301120333 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨10, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16744180216283 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193301120333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_11 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (10460782426607 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193305110427 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨11, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (10460782426607 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193305110427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_12 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83651642202783 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193309121217 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨12, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83651642202783 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193309121217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_13 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (5226065588551 / 6250000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193313158491 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨13, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (5226065588551 / 6250000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193313158491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_14 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (334329924083 / 400000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096658584803 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨14, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (334329924083 / 400000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096658584803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_15 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41773968490281 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193321159789 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨15, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41773968490281 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193321159789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_16 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41756708631201 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (34270706129 / 1562500000000 : ℝ))
      (E := (cell13203 ⟨16, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41756708631201 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (34270706129 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_17 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16695784366519 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096664606783 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨17, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16695784366519 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096664606783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_18 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83444450657641 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193333228219 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨18, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83444450657641 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193333228219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_19 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41705001852107 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87733489619 / 4000000000000 : ℝ))
      (E := (cell13203 ⟨19, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41705001852107 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87733489619 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13204_0 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (1313572760649 / 1562500000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193150995083 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨0, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (1313572760649 / 1562500000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193150995083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_1 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (16806753700653 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (43863100647 / 2000000000000 : ℝ))
      (E := (cell13204 ⟨1, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (16806753700653 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (43863100647 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_2 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (1049986314217 / 1250000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193159018649 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨2, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (1049986314217 / 1250000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193159018649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_3 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (8396406654759 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096581539071 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨3, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (8396406654759 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096581539071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_4 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20982313174479 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219316710311 / 10000000000000 : ℝ))
      (E := (cell13204 ⟨4, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20982313174479 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219316710311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_5 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (16778892710497 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438634220269 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨5, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (16778892710497 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438634220269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_6 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (16771939815127 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193175080383 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨6, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (16771939815127 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193175080383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_7 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83824959231889 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193179105529 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨7, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83824959231889 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193179105529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_8 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20947560996489 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (27414789073 / 1250000000000 : ℝ))
      (E := (cell13204 ⟨8, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20947560996489 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (27414789073 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_9 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (8375555330273 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (34268549189 / 1562500000000 : ℝ))
      (E := (cell13204 ⟨9, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (8375555330273 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (34268549189 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_10 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (10465110893411 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (87727647153 / 4000000000000 : ℝ))
      (E := (cell13204 ⟨10, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (10465110893411 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (87727647153 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_11 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41843122742443 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548298791549 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨11, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41843122742443 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548298791549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_12 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41825814140483 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219319917431 / 10000000000000 : ℝ))
      (E := (cell13204 ⟨12, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41825814140483 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219319917431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_13 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41808517750573 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096601604477 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨13, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41808517750573 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096601604477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_14 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83582467111223 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096603608743 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨14, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83582467111223 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096603608743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_15 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83547923077171 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096605631671 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨15, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83547923077171 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096605631671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_16 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83513403365141 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274151904389 / 12500000000000 : ℝ))
      (E := (cell13204 ⟨16, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83513403365141 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274151904389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_17 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (4173945397073 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193219253979 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨17, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (4173945397073 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193219253979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_18 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83444436772627 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438644664903 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨18, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83444436772627 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438644664903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_19 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41704994912657 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193227334447 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨19, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41704994912657 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193227334447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13205_0 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (2627145083989 / 3125000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137065067451 / 6250000000000 : ℝ))
      (E := (cell13205 ⟨0, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (2627145083989 / 3125000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137065067451 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_1 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (84033754515589 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548261278323 / 25000000000000 : ℝ))
      (E := (cell13205 ⟨1, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (84033754515589 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548261278323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_2 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83998891155891 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137065572147 / 6250000000000 : ℝ))
      (E := (cell13205 ⟨2, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83998891155891 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137065572147 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_3 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83964052572323 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193053152841 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨3, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83964052572323 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193053152841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_4 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (20982309682211 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096528587379 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨4, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (20982309682211 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096528587379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_5 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83894449589603 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193061169989 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨5, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83894449589603 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193061169989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_6 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41929842559469 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193065204069 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨6, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41929842559469 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193065204069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_7 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83824945281371 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193069226329 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨7, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83824945281371 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193069226329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_8 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83790230041611 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193073243801 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨8, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83790230041611 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193073243801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_9 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41877769682277 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193077263263 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨9, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41877769682277 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193077263263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_10 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83720873215273 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548270308289 / 25000000000000 : ℝ))
      (E := (cell13205 ⟨10, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83720873215273 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548270308289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_11 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83686231559029 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (27413565949 / 1250000000000 : ℝ))
      (E := (cell13205 ⟨11, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83686231559029 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (27413565949 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_12 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83651614361261 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193089281381 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨12, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83651614361261 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193089281381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_13 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83617021587587 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109654665671 / 5000000000000 : ℝ))
      (E := (cell13205 ⟨13, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83617021587587 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109654665671 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_14 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (20895613300951 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438619463879 / 20000000000000 : ℝ))
      (E := (cell13205 ⟨14, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (20895613300951 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438619463879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_15 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5221744323493 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193101362739 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨15, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5221744323493 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193101362739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_16 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (20878347367497 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548276333011 / 25000000000000 : ℝ))
      (E := (cell13205 ⟨16, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (20878347367497 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548276333011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_17 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5217430878277 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193109348493 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨17, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5217430878277 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193109348493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_18 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41722211444859 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096556679189 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨18, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41722211444859 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096556679189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_19 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (2085249398713 / 2500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193117424263 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨19, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (2085249398713 / 2500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193117424263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13206_0 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (42034314347941 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548232804259 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨0, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (42034314347941 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548232804259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_1 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16806748106007 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274116905993 / 12500000000000 : ℝ))
      (E := (cell13206 ⟨1, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16806748106007 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274116905993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_2 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83998877176543 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096469613989 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨2, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83998877176543 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096469613989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_3 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41982019299587 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (21929432813 / 1000000000000 : ℝ))
      (E := (cell13206 ⟨3, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41982019299587 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (21929432813 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_4 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (8392922476189 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192947300191 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨4, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (8392922476189 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192947300191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_5 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83894435628839 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096475646221 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨5, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83894435628839 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096475646221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_6 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83859671164357 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192955323589 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨6, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83859671164357 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192955323589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_7 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (10478116416621 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548239835741 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨7, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (10478116416621 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548239835741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_8 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83790216099381 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192963357597 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨8, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83790216099381 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192963357597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_9 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (8375552542849 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192967374269 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨9, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (8375552542849 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192967374269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_10 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (20930214821343 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (438594268283 / 20000000000000 : ℝ))
      (E := (cell13206 ⟨10, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (20930214821343 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (438594268283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_11 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (20921554408821 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192975381481 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨11, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (20921554408821 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192975381481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_12 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41825800221833 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548244846073 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨12, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41825800221833 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548244846073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_13 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83617007676137 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192983413727 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨13, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83617007676137 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192983413727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_14 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41791219649247 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274123427143 / 12500000000000 : ℝ))
      (E := (cell13206 ⟨14, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41791219649247 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274123427143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_15 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83547895276713 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192991457977 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨15, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83547895276713 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192991457977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_16 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41756687788471 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192995483051 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨16, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41756687788471 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2192995483051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_17 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (8347888016551 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096499748553 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨17, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (8347888016551 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096499748553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_18 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16688881801783 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193003504643 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨18, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16688881801783 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193003504643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_19 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83409962073829 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096503754963 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨19, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83409962073829 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096503754963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13207_0 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (42034307353119 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192821350687 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨0, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (42034307353119 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192821350687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_1 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (84033726546601 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192825378429 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨1, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (84033726546601 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192825378429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_2 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41999431599657 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192829355343 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨2, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41999431599657 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192829355343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_3 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (16792804925629 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274104175699 / 12500000000000 : ℝ))
      (E := (cell13207 ⟨3, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (16792804925629 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274104175699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_4 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41964605398527 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096418710729 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨4, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41964605398527 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096418710729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_5 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83894421670191 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219284141073 / 10000000000000 : ℝ))
      (E := (cell13207 ⟨5, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83894421670191 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219284141073 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_6 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20964914302973 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096422719473 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨6, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20964914302973 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096422719473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_7 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (2095622934667 / 2500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548212363859 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨7, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (2095622934667 / 2500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548212363859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_8 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (16758040431853 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192853467231 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨8, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (16758040431853 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192853467231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_9 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (4187775574727 / 5000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274107185139 / 12500000000000 : ℝ))
      (E := (cell13207 ⟨9, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (4187775574727 / 5000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274107185139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_10 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41860422678791 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192861503607 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨10, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41860422678791 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192861503607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_11 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83686203713649 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192865541 / 100000000000 : ℝ))
      (E := (cell13207 ⟨11, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83686203713649 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192865541 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_12 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83651586528181 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (34263586581 / 1562500000000 : ℝ))
      (E := (cell13207 ⟨12, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83651586528181 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (34263586581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_13 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83616993766797 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192873568039 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨13, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83616993766797 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192873568039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_14 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83582425395293 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096438784461 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨14, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83582425395293 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096438784461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_15 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (16709576275929 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (109644077453 / 5000000000000 : ℝ))
      (E := (cell13207 ⟨15, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (16709576275929 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (109644077453 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_16 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83513361686003 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219288557167 / 10000000000000 : ℝ))
      (E := (cell13207 ⟨16, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83513361686003 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219288557167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_17 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83478866280693 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192889583309 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨17, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83478866280693 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192889583309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_18 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (10430549391277 / 12500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548223411689 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨18, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (10430549391277 / 12500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548223411689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_19 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83409948201243 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096448824869 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨19, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83409948201243 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096448824869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13208_0 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (16813720143743 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219271148017 / 10000000000000 : ℝ))
      (E := (cell13208 ⟨0, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (16813720143743 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219271148017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_1 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (84033712565287 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096357752373 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨1, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (84033712565287 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096357752373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_2 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20999712306051 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192719536447 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨2, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20999712306051 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192719536447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_3 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (83964010659233 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192723525719 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨3, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (83964010659233 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192723525719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_4 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (2622787401073 / 3125000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192727538559 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨4, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (2622787401073 / 3125000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192727538559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_5 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (4194720385683 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219273158283 / 10000000000000 : ℝ))
      (E := (cell13208 ⟨5, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (4194720385683 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219273158283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_6 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41929821630771 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192735608139 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨6, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41929821630771 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192735608139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_7 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41912451721253 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192739621769 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨7, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41912451721253 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192739621769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_8 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41895094110631 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (8770974523 / 400000000000 : ℝ))
      (E := (cell13208 ⟨8, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41895094110631 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (8770974523 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_9 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41877748781351 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274093455233 / 12500000000000 : ℝ))
      (E := (cell13208 ⟨9, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41877748781351 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274093455233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_10 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (2616275982247 / 3125000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (54818791541 / 2500000000000 : ℝ))
      (E := (cell13208 ⟨10, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (2616275982247 / 3125000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (54818791541 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_11 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (669489518353 / 800000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548188909561 / 25000000000000 : ℝ))
      (E := (cell13208 ⟨11, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (669489518353 / 800000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548188909561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_12 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41825786307403 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096379846959 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨12, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41825786307403 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096379846959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_13 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (16723395971913 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096381859097 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨13, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (16723395971913 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096381859097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_14 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (417912057471 / 500000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (34261995571 / 1562500000000 : ℝ))
      (E := (cell13208 ⟨14, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (417912057471 / 500000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (34261995571 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_15 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20886966871171 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096385876203 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨15, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20886966871171 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096385876203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_16 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (8351334779717 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192775714367 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨16, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (8351334779717 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192775714367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_17 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41739426198991 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219277978187 / 10000000000000 : ℝ))
      (E := (cell13208 ⟨17, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41739426198991 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219277978187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_18 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (83444381253621 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548195946179 / 25000000000000 : ℝ))
      (E := (cell13208 ⟨18, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (83444381253621 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548195946179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_19 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (83409934330759 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (10963938927 / 500000000000 : ℝ))
      (E := (cell13208 ⟨19, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (83409934330759 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (10963938927 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13209_0 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (328392916927 / 390625000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438520332669 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨0, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (328392916927 / 390625000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438520332669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_1 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (84033698586093 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192605684779 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨1, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (84033698586093 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192605684779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_2 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83998835251213 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096304856693 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨2, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83998835251213 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096304856693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_3 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (2099099917311 / 2500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192613699609 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨3, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (2099099917311 / 2500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192613699609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_4 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41964591436867 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (43852354189 / 2000000000000 : ℝ))
      (E := (cell13209 ⟨4, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41964591436867 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (43852354189 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_5 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (20973598439811 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (137038859423 / 6250000000000 : ℝ))
      (E := (cell13209 ⟨5, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (20973598439811 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (137038859423 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_6 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83859629313307 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219262577317 / 10000000000000 : ℝ))
      (E := (cell13209 ⟨6, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83859629313307 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219262577317 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_7 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83824889500447 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (109631489197 / 5000000000000 : ℝ))
      (E := (cell13209 ⟨7, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83824889500447 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (109631489197 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_8 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (20947543571343 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192633790109 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨8, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (20947543571343 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192633790109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_9 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83755483632977 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192637798457 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨9, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83755483632977 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192637798457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_10 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83720817508337 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438528363103 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨10, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83720817508337 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438528363103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_11 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (10460771984589 / 12500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096322923781 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨11, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (10460771984589 / 12500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096322923781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_12 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83651558703541 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438529968499 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨12, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83651558703541 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438529968499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_13 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41808482977221 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192653864193 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨13, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41808482977221 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192653864193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_14 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41791198797607 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192657860011 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨14, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41791198797607 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192657860011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_15 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (8354785359183 / 10000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548165473347 / 25000000000000 : ℝ))
      (E := (cell13209 ⟨15, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (8354785359183 / 10000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548165473347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_16 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41756666955221 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438533182229 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨16, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41756666955221 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438533182229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_17 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (667830708139 / 800000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192669918023 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨17, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (667830708139 / 800000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192669918023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_18 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (8344436737913 / 10000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548168479631 / 25000000000000 : ℝ))
      (E := (cell13209 ⟨18, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (8344436737913 / 10000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548168479631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_19 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83409920462379 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192677975213 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨19, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83409920462379 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192677975213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13210_0 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (84068572750029 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192491842353 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨0, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (84068572750029 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192491842353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_1 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (42016842304509 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096247930323 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨1, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (42016842304509 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096247930323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_2 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (4199941064017 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192499886159 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨2, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (4199941064017 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192499886159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_3 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83963982727763 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192503869337 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨3, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83963982727763 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192503869337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_4 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (5245573057203 / 6250000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219250793413 / 10000000000000 : ℝ))
      (E := (cell13210 ⟨4, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (5245573057203 / 6250000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219250793413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_5 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (2621699368967 / 3125000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096255957271 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨5, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (2621699368967 / 3125000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096255957271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_6 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83859615367187 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096257967019 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨6, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83859615367187 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096257967019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_7 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (167649751121 / 200000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192519941951 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨7, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (167649751121 / 200000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192519941951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_8 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16758032070319 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192523945307 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨8, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16758032070319 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192523945307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_9 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83755469705363 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1712912507 / 78125000000 : ℝ))
      (E := (cell13210 ⟨9, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83755469705363 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1712912507 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_10 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83720803586881 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192532023323 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨10, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83720803586881 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192532023323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_11 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (1307596280647 / 1562500000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192535994607 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨11, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (1307596280647 / 1562500000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192535994607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_12 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (5228221549649 / 6250000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (438508009011 / 20000000000000 : ℝ))
      (E := (cell13210 ⟨12, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (5228221549649 / 6250000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (438508009011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_13 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83616952051427 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192544064199 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨13, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83616952051427 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192544064199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_14 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16716476739667 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219254805751 / 10000000000000 : ℝ))
      (E := (cell13210 ⟨14, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16716476739667 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219254805751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_15 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41773919850541 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096276044213 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨15, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41773919850541 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096276044213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_16 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83513320025819 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192556103769 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨16, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83513320025819 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192556103769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_17 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83478824638873 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (54814002707 / 2500000000000 : ℝ))
      (E := (cell13210 ⟨17, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83478824638873 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (54814002707 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_18 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41722176753371 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192564106461 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨18, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41722176753371 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192564106461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_19 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (834099065961 / 1000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548142040219 / 25000000000000 : ℝ))
      (E := (cell13210 ⟨19, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (834099065961 / 1000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548142040219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13211_0 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (42034279384433 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438476415011 / 20000000000000 : ℝ))
      (E := (cell13211 ⟨0, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (42034279384433 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438476415011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_1 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (84033670634061 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274048261279 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨1, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (84033670634061 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274048261279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_2 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (2624962728487 / 3125000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (219239005477 / 10000000000000 : ℝ))
      (E := (cell13211 ⟨2, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (2624962728487 / 3125000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (219239005477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_3 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83963968765203 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192394092831 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨3, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83963968765203 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192394092831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_4 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41964577479439 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274049762087 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨4, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41964577479439 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274049762087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_5 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41947182928379 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548100533033 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨5, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41947182928379 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548100533033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_6 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (4192980071159 / 5000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548101537187 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨6, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (4192980071159 / 5000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548101537187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_7 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83824861622667 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (87696406153 / 4000000000000 : ℝ))
      (E := (cell13211 ⟨7, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83824861622667 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (87696406153 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_8 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83790146419929 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438482830879 / 20000000000000 : ℝ))
      (E := (cell13211 ⟨8, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83790146419929 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438482830879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_9 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (4187772788993 / 5000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096209107653 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨9, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (4187772788993 / 5000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096209107653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_10 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16744157933507 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (68513194593 / 3125000000000 : ℝ))
      (E := (cell13211 ⟨10, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16744157933507 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (68513194593 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_11 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41843074024107 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548106548903 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨11, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41843074024107 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548106548903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_12 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16730306177467 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192430243461 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨12, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16730306177467 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192430243461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_13 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83616938150519 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192434260051 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨13, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83616938150519 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192434260051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_14 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41791184901781 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274054781357 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨14, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41791184901781 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274054781357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_15 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83547825812439 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192442279313 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨15, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83547825812439 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192442279313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_16 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83513306143301 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192446292243 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨16, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83513306143301 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192446292243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_17 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41739405381237 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548112588161 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨17, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41739405381237 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548112588161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_18 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83444339636457 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192454348529 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨18, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83444339636457 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192454348529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_19 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (20852473182981 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192458342391 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨19, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (20852473182981 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192458342391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13212_0 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (42034272394911 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192272303593 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨0, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (42034272394911 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192272303593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_1 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (84033656661223 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096138157827 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨1, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (84033656661223 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096138157827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_2 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41999396672473 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192280335029 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨2, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41999396672473 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192280335029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_3 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (2099098870119 / 2500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096142156081 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨3, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (2099098870119 / 2500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096142156081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_4 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (5245571312789 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192288313053 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨4, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (5245571312789 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192288313053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_5 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83894351908687 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192292345563 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨5, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83894351908687 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192292345563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_6 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83859587481287 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192296359297 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨6, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83859587481287 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192296359297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_7 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83824847686947 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192300361541 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨7, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83824847686947 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192300361541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_8 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (10473766561297 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219230441737 / 10000000000000 : ℝ))
      (E := (cell13212 ⟨8, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (10473766561297 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219230441737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_9 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83755441856467 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192308417497 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨9, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83755441856467 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192308417497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_10 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83720775750299 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192312426473 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨10, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83720775750299 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192312426473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_11 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (10460766767141 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109615822529 / 5000000000000 : ℝ))
      (E := (cell13212 ⟨11, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (10460766767141 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109615822529 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_12 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16730303396479 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548080123963 / 25000000000000 : ℝ))
      (E := (cell13212 ⟨12, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16730303396479 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548080123963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_13 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41808462125859 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096162254957 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨13, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41808462125859 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096162254957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_14 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16716471182179 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192328498237 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨14, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16716471182179 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192328498237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_15 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83547811925901 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096166262129 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨15, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83547811925901 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096166262129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_16 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83513292262887 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192336534799 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨16, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83513292262887 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192336534799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_17 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41739398444089 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096170267301 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨17, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41739398444089 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096170267301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_18 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41722162884137 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (137021536653 / 6250000000000 : ℝ))
      (E := (cell13212 ⟨18, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41722162884137 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (137021536653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_19 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83409878869849 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192348578061 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨19, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83409878869849 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192348578061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13213_0 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (2627141587903 / 3125000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (68505078999 / 3125000000000 : ℝ))
      (E := (cell13213 ⟨0, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (2627141587903 / 3125000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (68505078999 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_1 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (84033642690503 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192166536913 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨1, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (84033642690503 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192166536913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_2 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (3359951175217 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192170553221 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨2, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (3359951175217 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192170553221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_3 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (2623873151451 / 3125000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192174585263 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨3, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (2623873151451 / 3125000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192174585263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_4 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20982281763121 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548044645801 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨4, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20982281763121 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548044645801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_5 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (8389433796273 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219218261281 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨5, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (8389433796273 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219218261281 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_6 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83859573541507 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274023327961 / 12500000000000 : ℝ))
      (E := (cell13213 ⟨6, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83859573541507 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274023327961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_7 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41912416876669 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192190623123 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨7, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41912416876669 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192190623123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_8 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83790118562933 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219219467619 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨8, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83790118562933 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219219467619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_9 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (16751085587037 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192198673601 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨9, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (16751085587037 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192198673601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_10 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20930190458793 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548050669977 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨10, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20930190458793 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548050669977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_11 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83686120228151 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192206701393 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨11, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83686120228151 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192206701393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_12 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41825751539781 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192210685951 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨12, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41825751539781 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192210685951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_13 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (5226056897189 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274026844453 / 12500000000000 : ℝ))
      (E := (cell13213 ⟨13, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (5226056897189 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274026844453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_14 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41791171010167 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096109370733 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨14, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41791171010167 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096109370733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_15 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20886949510367 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192222765053 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨15, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20886949510367 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192222765053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_16 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (1304894974759 / 1562500000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096113386603 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨16, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (1304894974759 / 1562500000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096113386603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_17 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (16695756603197 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192230770667 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨17, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (16695756603197 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192230770667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_18 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83444311902193 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192234820219 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨18, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83444311902193 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192234820219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_19 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41704932504937 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438447761917 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨19, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41704932504937 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438447761917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13214_0 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (84068516838089 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096026403019 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨0, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (84068516838089 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096026403019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_1 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (84033628721899 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096028405947 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨1, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (84033628721899 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096028405947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_2 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (4199938270901 / 5000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192060825157 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨2, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (4199938270901 / 5000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192060825157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_3 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (4198196344511 / 5000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192064854203 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨3, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (4198196344511 / 5000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192064854203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_4 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83929113102459 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096034424597 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨4, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83929113102459 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096034424597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_5 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83894324018887 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192072875897 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨5, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83894324018887 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192072875897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_6 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83859559603839 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096038441961 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨6, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83859559603839 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096038441961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_7 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83824819821841 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192080880547 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨7, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83824819821841 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192080880547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_8 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83790104637601 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192084930853 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨8, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83790104637601 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192084930853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_9 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83755414016013 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192088925549 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨9, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83755414016013 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192088925549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_10 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83720747922153 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192092929189 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨10, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83720747922153 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192092929189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_11 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83686106321281 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096048474027 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨11, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83686106321281 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096048474027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_12 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16730297835767 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192100988177 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨12, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16730297835767 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192100988177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_13 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16723379292087 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (34251640581 / 1562500000000 : ℝ))
      (E := (cell13214 ⟨13, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16723379292087 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (34251640581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_14 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41791164065939 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192109038731 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨14, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41791164065939 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192109038731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_15 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83547784159139 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096056500849 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨15, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83547784159139 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096056500849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_16 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83513264508369 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192117065697 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨16, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83513264508369 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192117065697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_17 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41739384572947 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096060530421 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨17, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41739384572947 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096060530421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_18 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83444298038213 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192125049843 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨18, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83444298038213 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192125049843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_19 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (5213115697 / 6250000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438425819053 / 20000000000000 : ℝ))
      (E := (cell13214 ⟨19, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (5213115697 / 6250000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438425819053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13215_0 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (84068502865399 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191943079949 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨0, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (84068502865399 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191943079949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_1 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (21008403688853 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438389416543 / 20000000000000 : ℝ))
      (E := (cell13215 ⟨1, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (21008403688853 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438389416543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_2 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (8399875145773 / 10000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (273993886617 / 12500000000000 : ℝ))
      (E := (cell13215 ⟨2, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (8399875145773 / 10000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (273993886617 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_3 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41981956468061 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1095977559493 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨3, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41981956468061 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1095977559493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_4 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20982274788637 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (547989777757 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨4, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20982274788637 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (547989777757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_5 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20973577519289 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219196313483 / 10000000000000 : ℝ))
      (E := (cell13215 ⟨5, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20973577519289 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219196313483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_6 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20964886417071 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191967139999 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨6, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20964886417071 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191967139999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_7 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16764961178491 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (13699819949 / 625000000000 : ℝ))
      (E := (cell13215 ⟨7, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16764961178491 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (13699819949 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_8 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83790090714379 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191975181363 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨8, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83790090714379 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191975181363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_9 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (1675108001979 / 2000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438395846283 / 20000000000000 : ℝ))
      (E := (cell13215 ⟨9, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (1675108001979 / 2000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438395846283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_10 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83720734011243 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191983232411 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨10, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83720734011243 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191983232411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_11 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83686092416519 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191987248679 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨11, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83686092416519 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191987248679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_12 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16730295056043 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191991286253 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨12, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16730295056043 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191991286253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_13 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (5226055160497 / 6250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (547998823189 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨13, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (5226055160497 / 6250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (547998823189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_14 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83582314245527 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191999273661 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨14, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83582314245527 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2191999273661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_15 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41773885139457 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548000823101 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨15, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41773885139457 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548000823101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_16 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16702650126853 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192007354041 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨16, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16702650126853 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192007354041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_17 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16695751055581 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219201134687 / 10000000000000 : ℝ))
      (E := (cell13215 ⟨17, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16695751055581 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219201134687 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_18 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16688856835267 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096007695941 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨18, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16688856835267 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096007695941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_19 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83409837296227 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192019376801 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨19, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83409837296227 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192019376801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13216_0 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (42034244447413 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095916674849 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨0, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (42034244447413 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095916674849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_1 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (42016800395521 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191837407257 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨1, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (42016800395521 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191837407257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_2 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (20999684374889 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109592070723 / 5000000000000 : ℝ))
      (E := (cell13216 ⟨2, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (20999684374889 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109592070723 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_3 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83963898984139 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191845437539 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨3, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83963898984139 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191845437539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_4 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (67143268167 / 80000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191849426657 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨4, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (67143268167 / 80000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191849426657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_5 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41947148068769 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095926723791 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨5, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41947148068769 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095926723791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_6 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (2096488293371 / 2500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (6849554531 / 312500000000 : ℝ))
      (E := (cell13216 ⟨6, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (2096488293371 / 2500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (6849554531 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_7 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (4191239598259 / 5000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191861498979 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨7, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (4191239598259 / 5000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191861498979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_8 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83790076793267 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438373097153 / 20000000000000 : ℝ))
      (E := (cell13216 ⟨8, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83790076793267 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438373097153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_9 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16751077236799 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (273983691641 / 12500000000000 : ℝ))
      (E := (cell13216 ⟨9, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16751077236799 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (273983691641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_10 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83720720102441 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191873531481 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨10, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83720720102441 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191873531481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_11 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83686078513863 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095938772577 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨11, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83686078513863 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095938772577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_12 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83651461383701 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191881580179 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨12, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83651461383701 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191881580179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_13 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41808434338787 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109594279209 / 5000000000000 : ℝ))
      (E := (cell13216 ⟨13, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41808434338787 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109594279209 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_14 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83582300361279 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (136993101301 / 6250000000000 : ℝ))
      (E := (cell13216 ⟨14, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83582300361279 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (136993101301 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_15 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (10443469550099 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095946818587 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨15, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (10443469550099 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095946818587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_16 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41756618381131 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191897638239 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨16, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41756618381131 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191897638239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_17 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83478741412017 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191901628753 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨17, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83478741412017 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191901628753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_18 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (20861067579139 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (273988208937 / 12500000000000 : ℝ))
      (E := (cell13216 ⟨18, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (20861067579139 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (273988208937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_19 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (10426227930319 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191909712497 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨19, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (10426227930319 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191909712497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13217_0 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8406847492637 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191723673147 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨0, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8406847492637 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191723673147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_1 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (84033586828787 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095863863821 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨1, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (84033586828787 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095863863821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_2 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83998723543497 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191731731827 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨2, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83998723543497 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191731731827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_3 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83963885034269 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (8561467781 / 390625000000 : ℝ))
      (E := (cell13217 ⟨3, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83963885034269 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (8561467781 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_4 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16785814253013 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (219173973813 / 10000000000000 : ℝ))
      (E := (cell13217 ⟨4, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16785814253013 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (219173973813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_5 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83894282200031 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (109587187809 / 5000000000000 : ℝ))
      (E := (cell13217 ⟨5, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83894282200031 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (109587187809 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_6 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83859517803507 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273968476711 / 12500000000000 : ℝ))
      (E := (cell13217 ⟨6, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83859517803507 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273968476711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_7 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16764955608003 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191751801963 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨7, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16764955608003 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191751801963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_8 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (10473757859283 / 12500000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191755844061 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨8, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (10473757859283 / 12500000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191755844061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_9 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83755372271149 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (68492494709 / 3125000000000 : ℝ))
      (E := (cell13217 ⟨9, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83755372271149 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (68492494709 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_10 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41860353097873 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095881942247 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨10, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41860353097873 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095881942247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_11 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41843032306657 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438353579119 / 20000000000000 : ℝ))
      (E := (cell13217 ⟨11, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41843032306657 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438353579119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_12 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83651447489293 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095885934977 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨12, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83651447489293 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095885934977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_13 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (836168547893 / 1000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191775929619 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨13, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (836168547893 / 1000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191775929619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_14 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16716457295827 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191779905637 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨14, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16716457295827 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191779905637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_15 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20886935631193 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191783919587 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨15, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20886935631193 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191783919587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_16 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41756611446181 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547946994131 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨16, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41756611446181 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547946994131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_17 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8347872754823 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191791964747 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨17, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8347872754823 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191791964747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_18 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83444256458877 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191796005247 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨18, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83444256458877 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191796005247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_19 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (1303278274859 / 1562500000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095899992873 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨19, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (1303278274859 / 1562500000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095899992873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13218_0 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (8406846096003 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095807025149 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨0, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (8406846096003 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095807025149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_1 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (84033572868647 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191618043869 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨1, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (84033572868647 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191618043869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_2 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (5249919349347 / 6250000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191622045037 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨2, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (5249919349347 / 6250000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191622045037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_3 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83963871086513 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191626062177 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨3, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83963871086513 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191626062177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_4 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (20982264330873 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095815051701 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨4, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (20982264330873 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095815051701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_5 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83894268264637 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095817059299 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨5, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83894268264637 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095817059299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_6 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (20964875968571 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095819057651 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨6, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (20964875968571 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095819057651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_7 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83824764116959 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (109582107941 / 5000000000000 : ℝ))
      (E := (cell13218 ⟨7, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83824764116959 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (109582107941 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_8 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (8379004895737 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095823070079 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨8, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (8379004895737 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095823070079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_9 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83755358360411 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273956272771 / 12500000000000 : ℝ))
      (E := (cell13218 ⟨9, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83755358360411 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273956272771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_10 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41860346145579 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191654175263 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨10, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41860346145579 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191654175263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_11 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83686050714871 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191658241887 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨11, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83686050714871 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191658241887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_12 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83651433596989 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191662213723 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨12, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83651433596989 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191662213723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_13 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83616840903131 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191666270909 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨13, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83616840903131 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191666270909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_14 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16716454519819 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191670244497 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨14, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16716454519819 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191670244497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_15 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16709545730171 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (34244910251 / 1562500000000 : ℝ))
      (E := (cell13218 ⟨15, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16709545730171 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (34244910251 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_16 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41756604512281 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095839155333 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨16, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41756604512281 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095839155333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_17 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (5217419605409 / 6250000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191682296597 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨17, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (5217419605409 / 6250000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191682296597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_18 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41722121301649 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095843167427 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨18, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41722121301649 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095843167427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_19 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83409795741499 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191690371461 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨19, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83409795741499 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191690371461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13219_0 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (42034223497903 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191504423291 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨0, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (42034223497903 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191504423291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_1 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (42016779455311 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191508413823 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨1, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (42016779455311 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191508413823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_2 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83998695637721 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095756205999 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨2, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83998695637721 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095756205999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_3 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (8396385714087 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136969776637 / 6250000000000 : ℝ))
      (E := (cell13219 ⟨3, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (8396385714087 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136969776637 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_4 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83929043384031 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (54788011613 / 2500000000000 : ℝ))
      (E := (cell13219 ⟨4, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83929043384031 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (54788011613 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_5 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83894254331353 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (34242569951 / 1562500000000 : ℝ))
      (E := (cell13219 ⟨5, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83894254331353 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (34242569951 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_6 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20964872486793 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547882117691 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨6, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20964872486793 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547882117691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_7 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20956187549003 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (87661300461 / 4000000000000 : ℝ))
      (E := (cell13219 ⟨7, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20956187549003 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (87661300461 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_8 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (10473754380323 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191536548199 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨8, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (10473754380323 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191536548199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_9 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83755344451779 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191540529499 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨9, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83755344451779 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191540529499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_10 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20930169597169 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191544578071 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨10, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20930169597169 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191544578071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_11 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83686036818533 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191548584031 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨11, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83686036818533 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191548584031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_12 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (8365141970679 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547888152871 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨12, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (8365141970679 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547888152871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_13 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (16723365403813 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (438311321611 / 20000000000000 : ℝ))
      (E := (cell13219 ⟨13, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (16723365403813 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (438311321611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_14 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83582258721157 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (10957803187 / 500000000000 : ℝ))
      (E := (cell13219 ⟨14, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83582258721157 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (10957803187 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_15 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83547714779039 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136972790413 / 6250000000000 : ℝ))
      (E := (cell13219 ⟨15, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83547714779039 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136972790413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_16 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (5219574697429 / 6250000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095784320331 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨16, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (5219574697429 / 6250000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095784320331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_17 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83478699826957 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191572682563 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨17, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83478699826957 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191572682563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_18 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (41722114374909 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (10957883593 / 500000000000 : ℝ))
      (E := (cell13219 ⟨18, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (41722114374909 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (10957883593 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_19 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (2085244547353 / 2500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (219158069473 / 10000000000000 : ℝ))
      (E := (cell13219 ⟨19, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (2085244547353 / 2500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (219158069473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13220_0 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (84068433033697 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (34240543627 / 1562500000000 : ℝ))
      (E := (cell13220 ⟨0, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (84068433033697 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (34240543627 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_1 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (10504193119339 / 12500000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191398779621 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨1, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (10504193119339 / 12500000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191398779621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_2 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83998681688003 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273925354089 / 12500000000000 : ℝ))
      (E := (cell13220 ⟨2, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83998681688003 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273925354089 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_3 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (4198192159867 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136962927749 / 6250000000000 : ℝ))
      (E := (cell13220 ⟨3, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (4198192159867 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136962927749 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_4 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41964514723341 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438282164297 / 20000000000000 : ℝ))
      (E := (cell13220 ⟨4, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41964514723341 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438282164297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_5 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (4194712020009 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191414830979 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨5, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (4194712020009 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191414830979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_6 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83859476022169 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547854720019 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨6, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83859476022169 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547854720019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_7 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (3352989451087 / 4000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095711459051 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨7, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (3352989451087 / 4000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095711459051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_8 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16758004225981 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438285378809 / 20000000000000 : ℝ))
      (E := (cell13220 ⟨8, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16758004225981 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438285378809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_9 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16751066109051 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (34241108293 / 1562500000000 : ℝ))
      (E := (cell13220 ⟨9, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16751066109051 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (34241108293 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_10 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (837206644883 / 1000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095717459319 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨10, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (837206644883 / 1000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095717459319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_11 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83686022924301 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095719490073 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨11, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83686022924301 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095719490073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_12 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16730281163739 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (27393036837 / 1250000000000 : ℝ))
      (E := (cell13220 ⟨12, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16730281163739 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (27393036837 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_13 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41808406568551 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191446999219 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨13, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41808406568551 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191446999219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_14 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83582244845321 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191451026159 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨14, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83582244845321 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191451026159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_15 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (3341908036373 / 4000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191455033009 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨15, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (3341908036373 / 4000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191455033009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_16 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41756590647633 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191459024751 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨16, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41756590647633 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191459024751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_17 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83478685969469 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547865766097 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨17, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83478685969469 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547865766097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_18 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20861053724609 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095733549103 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨18, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20861053724609 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095733549103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_19 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83409768048839 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547867768041 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨19, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83409768048839 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547867768041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13221_0 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (84068419073703 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191285156809 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨0, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (84068419073703 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191285156809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_1 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (16806706200183 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547822299787 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨1, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (16806706200183 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547822299787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_2 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41999333870199 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438258638273 / 20000000000000 : ℝ))
      (E := (cell13221 ⟨2, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41999333870199 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438258638273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_3 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83963829255921 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191297199693 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨3, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83963829255921 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191297199693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_4 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20982253877861 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (8765204929 / 400000000000 : ℝ))
      (E := (cell13221 ⟨4, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20982253877861 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (8765204929 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_5 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83894226471117 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095652619459 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨5, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83894226471117 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095652619459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_6 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20964865524819 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547827321309 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨6, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20964865524819 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547827321309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_7 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (16764944472089 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191313262507 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨7, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (16764944472089 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191313262507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_8 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41895003609667 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547829323447 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨8, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41895003609667 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547829323447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_9 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83755316640837 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191321327857 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨9, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83755316640837 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191321327857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_10 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8372065059003 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191325313151 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨10, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8372065059003 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191325313151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_11 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20921502258043 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438265874423 / 20000000000000 : ℝ))
      (E := (cell13221 ⟨11, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20921502258043 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438265874423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_12 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83651391932703 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547833348643 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨12, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83651391932703 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547833348643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_13 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41808399628621 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191337386239 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨13, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41808399628621 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191337386239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_14 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41791115485793 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (87653656431 / 4000000000000 : ℝ))
      (E := (cell13221 ⟨14, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41791115485793 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (87653656431 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_15 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83547687041711 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191345415267 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨15, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83547687041711 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191345415267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_16 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83513167433767 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191349462933 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨16, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83513167433767 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191349462933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_17 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83478672114081 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (219135344207 / 10000000000000 : ℝ))
      (E := (cell13221 ⟨17, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83478672114081 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (219135344207 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_18 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (1303815641393 / 1562500000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273919684209 / 12500000000000 : ℝ))
      (E := (cell13221 ⟨18, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (1303815641393 / 1562500000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273919684209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_19 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41704877102827 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547840375941 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨19, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41704877102827 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547840375941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13222_0 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (5254275319739 / 6250000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438235115039 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨0, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (5254275319739 / 6250000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438235115039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_1 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (5252094815577 / 6250000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191179614521 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨1, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (5252094815577 / 6250000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191179614521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_2 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16799730758981 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547795900943 / 25000000000000 : ℝ))
      (E := (cell13222 ⟨2, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16799730758981 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547795900943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_3 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83963815316613 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191187667111 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨3, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83963815316613 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191187667111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_4 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20982250394579 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438238327773 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨4, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20982250394579 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438238327773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_5 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83894212544163 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438239140137 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨5, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83894212544163 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438239140137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_6 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83859448178491 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191199686247 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨6, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83859448178491 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191199686247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_7 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83824708445823 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191203718811 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨7, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83824708445823 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191203718811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_8 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (8378999331087 / 10000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (219120774743 / 10000000000000 : ℝ))
      (E := (cell13222 ⟨8, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (8378999331087 / 10000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (219120774743 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_9 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (3350212109541 / 4000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095605860407 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨9, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (3350212109541 / 4000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095605860407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_10 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (10465079586733 / 12500000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547803940403 / 25000000000000 : ℝ))
      (E := (cell13222 ⟨10, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (10465079586733 / 12500000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547803940403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_11 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20921498785537 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095609879969 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨11, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20921498785537 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095609879969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_12 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16730275609763 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095611889949 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨12, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16730275609763 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095611889949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_13 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20904196344871 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191227827279 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨13, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20904196344871 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191227827279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_14 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83582217099953 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438246369887 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨14, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83582217099953 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438246369887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_15 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41773836588099 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191235851593 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨15, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41773836588099 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191235851593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_16 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (2609786049199 / 3125000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191239838739 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨16, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (2609786049199 / 3125000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191239838739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_17 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83478658260791 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191243873871 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨17, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83478658260791 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191243873871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_18 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41722093600983 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191247903279 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨18, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41722093600983 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191247903279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_19 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41704870182283 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (87650077249 / 4000000000000 : ℝ))
      (E := (cell13222 ⟨19, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41704870182283 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (87650077249 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13223_0 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (42034195580029 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191066047289 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨0, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (42034195580029 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191066047289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_1 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (84033503099661 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095535012871 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨1, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (84033503099661 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095535012871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_2 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (3359945594061 / 4000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191074069933 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨2, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (3359945594061 / 4000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191074069933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_3 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83963801379417 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (17117797441 / 781250000000 : ℝ))
      (E := (cell13223 ⟨3, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83963801379417 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (17117797441 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_4 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83928987647299 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547770524821 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨4, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83928987647299 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547770524821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_5 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83894198619319 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095543050163 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨5, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83894198619319 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095543050163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_6 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41929717129907 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191090141111 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨6, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41929717129907 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191090141111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_7 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20956173633327 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273886771371 / 12500000000000 : ℝ))
      (E := (cell13223 ⟨7, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20956173633327 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273886771371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_8 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (2618436856391 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191098138879 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨8, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (2618436856391 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191098138879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_9 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41877644419159 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095551083849 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨9, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41877644419159 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095551083849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_10 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83720622799803 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191106205929 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨10, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83720622799803 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191106205929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_11 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83685981254227 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438222040347 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨11, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83685981254227 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438222040347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_12 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83651364167029 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095557109611 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨12, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83651364167029 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095557109611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_13 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20904192875957 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191118264177 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨13, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20904192875957 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191118264177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_14 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83582203230421 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095561141977 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨14, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83582203230421 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095561141977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_15 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (5221728707049 / 6250000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191126283781 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨15, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (5221728707049 / 6250000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191126283781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_16 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20878284929267 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (3505808523 / 160000000000 : ℝ))
      (E := (cell13223 ⟨16, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20878284929267 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (3505808523 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_17 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83478644409599 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191134301533 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨17, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83478644409599 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191134301533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_18 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83444173356877 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191138328749 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨18, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83444173356877 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191138328749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_19 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41704863262787 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191142354549 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨19, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41704863262787 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191142354549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13224_0 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (16813675441281 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (219095651523 / 10000000000000 : ℝ))
      (E := (cell13224 ⟨0, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (16813675441281 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (219095651523 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_1 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (84033489152203 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095480245347 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨1, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (84033489152203 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095480245347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_2 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (16799725182051 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438192906389 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨2, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (16799725182051 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438192906389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_3 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83963787444331 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438193706313 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨3, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83963787444331 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438193706313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_4 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83928973718391 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190972555553 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨4, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83928973718391 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190972555553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_5 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83894184696583 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438195310759 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨5, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83894184696583 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438195310759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_6 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (16771884068649 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190980591827 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨6, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (16771884068649 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190980591827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_7 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83824680622901 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190984618977 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨7, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83824680622901 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190984618977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_8 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (4189498275013 / 5000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190988642277 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨8, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (4189498275013 / 5000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190988642277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_9 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (10469409367527 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547748152609 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨9, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (10469409367527 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547748152609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_10 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41860304453923 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190996646101 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨10, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41860304453923 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2190996646101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_11 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83685967368409 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191000697507 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨11, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83685967368409 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191000697507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_12 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (16730270057469 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438200942509 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨12, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (16730270057469 / 20000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438200942509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_13 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (1306511837973 / 1562500000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438201739387 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨13, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (1306511837973 / 1562500000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438201739387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_14 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83582189362989 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191012714333 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨14, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83582189362989 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191012714333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_15 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (8354764545147 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547754177957 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨15, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (8354764545147 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547754177957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_16 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41756562930933 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191020752637 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨16, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41756562930933 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191020752637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_17 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (10434828820063 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438204956663 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨17, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (10434828820063 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438204956663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_18 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20861039878471 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191028808363 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨18, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20861039878471 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191028808363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_19 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41704856344339 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095516416021 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨19, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41704856344339 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095516416021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

end BstLean.Part268
