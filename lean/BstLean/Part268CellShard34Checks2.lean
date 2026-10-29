import BstLean.Part268CellShard34Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13200_40 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82692196879543 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438750301887 / 20000000000000 : ℝ))
      (E := (cell13200 ⟨40, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82692196879543 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438750301887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_41 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41329137343167 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274219443339 / 12500000000000 : ℝ))
      (E := (cell13200 ⟨41, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41329137343167 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274219443339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_42 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41312187996723 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096879778109 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨42, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41312187996723 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096879778109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_43 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (1290476574553 / 1562500000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096881797769 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨43, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (1290476574553 / 1562500000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096881797769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_44 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16511329798167 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096883802179 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨44, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16511329798167 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096883802179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_45 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16504564124517 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096885819939 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨45, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16504564124517 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096885819939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_46 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82489015637599 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193775641303 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨46, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82489015637599 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193775641303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_47 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82455234006979 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193779665451 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨47, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82455234006979 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193779665451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_48 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82421475701973 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193783710037 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨48, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82421475701973 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193783710037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_49 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82387740693971 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193787713557 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨49, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82387740693971 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193787713557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_50 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20588507238627 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193791732259 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨50, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20588507238627 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193791732259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_51 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (4116017022763 / 5000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274224470403 / 12500000000000 : ℝ))
      (E := (cell13200 ⟨51, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (4116017022763 / 5000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274224470403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_52 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41143337584023 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193799744243 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨52, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41143337584023 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193799744243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_53 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (10281629133103 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193803790103 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨53, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (10281629133103 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193803790103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_54 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41109707058847 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193807779079 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨54, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41109707058847 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193807779079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_55 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82185818298893 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096905912817 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨55, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82185818298893 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096905912817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_56 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20538061395199 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438763173341 / 20000000000000 : ℝ))
      (E := (cell13200 ⟨56, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20538061395199 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438763173341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_57 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41059347967959 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096909949059 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨57, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41059347967959 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096909949059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_58 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20521292334227 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274227989437 / 12500000000000 : ℝ))
      (E := (cell13200 ⟨58, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20521292334227 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (274227989437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_59 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82051665756553 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438765582851 / 20000000000000 : ℝ))
      (E := (cell13200 ⟨59, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82051665756553 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (438765582851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13201_40 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82692183121607 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548410379731 / 25000000000000 : ℝ))
      (E := (cell13201 ⟨40, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82692183121607 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548410379731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_41 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (20664565233601 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219364555487 / 10000000000000 : ℝ))
      (E := (cell13201 ⟨41, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (20664565233601 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219364555487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_42 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82624362247517 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193649563091 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨42, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82624362247517 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193649563091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_43 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41295243515729 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193653601173 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨43, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41295243515729 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193653601173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_44 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (20639158814223 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193657608801 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨44, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (20639158814223 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193657608801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_45 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (20630701723657 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193661643173 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨45, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (20630701723657 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193661643173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_46 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82489001915623 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096832821749 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨46, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82489001915623 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096832821749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_47 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82455220290979 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193669666593 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨47, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82455220290979 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193669666593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_48 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10302682748993 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193673710171 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨48, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10302682748993 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193673710171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_49 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82387726989909 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (274209714091 / 12500000000000 : ℝ))
      (E := (cell13201 ⟨49, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82387726989909 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (274209714091 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_50 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10294251907051 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438736346103 / 20000000000000 : ℝ))
      (E := (cell13201 ⟨50, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10294251907051 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438736346103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_51 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82320326763117 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219368576061 / 10000000000000 : ℝ))
      (E := (cell13201 ⟨51, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82320326763117 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219368576061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_52 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (16457332296371 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193689799881 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨52, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (16457332296371 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193689799881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_53 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82253019384581 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193693785887 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨53, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82253019384581 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193693785887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_54 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41109700221697 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193697833253 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨54, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41109700221697 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193697833253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_55 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (8218580463053 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193701820001 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨55, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (8218580463053 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193701820001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_56 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82152231918367 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193705860431 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨56, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82152231918367 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193705860431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_57 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82118682279417 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193709891251 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨57, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82118682279417 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193709891251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_58 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (20521288921583 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (27421423851 / 1250000000000 : ℝ))
      (E := (cell13201 ⟨58, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (20521288921583 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (27421423851 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_59 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10256456513987 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (68553684573 / 3125000000000 : ℝ))
      (E := (cell13201 ⟨59, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10256456513987 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (68553684573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13202_40 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41346084682879 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548382895767 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨40, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41346084682879 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548382895767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_41 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (1033228089807 / 1250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548383904427 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨41, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (1033228089807 / 1250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548383904427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_42 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (10328043562959 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193539624669 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨42, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (10328043562959 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193539624669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_43 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (10323809161701 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193543602671 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨43, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (10323809161701 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193543602671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_44 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (10319577690629 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548386916999 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨44, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (10319577690629 / 12500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548386916999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_45 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82522793168753 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096775821167 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨45, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82522793168753 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096775821167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_46 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (5155561762233 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (137097231281 / 6250000000000 : ℝ))
      (E := (cell13202 ⟨46, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (5155561762233 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (137097231281 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_47 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (4122760328853 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (6854874133 / 312500000000 : ℝ))
      (E := (cell13202 ⟨47, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (4122760328853 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (6854874133 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_48 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (16484289656799 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548390926543 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨48, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (16484289656799 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548390926543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_49 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41193856643963 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096783883387 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨49, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41193856643963 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096783883387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_50 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (16470800312077 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (219357178367 / 10000000000000 : ℝ))
      (E := (cell13202 ⟨50, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (16470800312077 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (219357178367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_51 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82320313073051 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096787906459 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨51, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82320313073051 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096787906459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_52 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (4114332389887 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096789896157 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨52, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (4114332389887 / 5000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096789896157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_53 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82253005706413 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096791918321 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨53, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82253005706413 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096791918321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_54 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82219386771167 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096793941651 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨54, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82219386771167 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096793941651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_55 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82185790964241 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096795934693 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨55, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82185790964241 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096795934693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_56 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (8215221825801 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096797954601 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨56, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (8215221825801 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096797954601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_57 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20529667156247 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548399984863 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨57, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20529667156247 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548399984863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_58 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41042571018913 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193603955757 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨58, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41042571018913 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193603955757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_59 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20512909617327 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (17137562137 / 781250000000 : ℝ))
      (E := (cell13202 ⟨59, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20512909617327 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (17137562137 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13203_40 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (20673038902999 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193421643073 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨40, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (20673038902999 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193421643073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_41 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82658233436801 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193425617589 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨41, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82658233436801 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193425617589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_42 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (10328041845239 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548357420527 / 25000000000000 : ℝ))
      (E := (cell13203 ⟨42, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (10328041845239 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548357420527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_43 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41295229778921 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193433658897 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨43, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41295229778921 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193433658897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_44 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16511321559051 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096718861527 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨44, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16511321559051 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096718861527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_45 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (515767371531 / 625000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193441696271 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨45, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (515767371531 / 625000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193441696271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_46 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41244487238957 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096722876679 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨46, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41244487238957 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096722876679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_47 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82455192865221 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (274181221799 / 12500000000000 : ℝ))
      (E := (cell13203 ⟨47, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82455192865221 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (274181221799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_48 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41210717289063 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193453757021 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨48, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41210717289063 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193453757021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_49 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82387699588021 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193457816687 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨49, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82387699588021 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193457816687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_50 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (2058849696661 / 2500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548365458173 / 25000000000000 : ℝ))
      (E := (cell13203 ⟨50, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (2058849696661 / 2500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548365458173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_51 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82320299385061 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (274183232637 / 12500000000000 : ℝ))
      (E := (cell13203 ⟨51, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82320299385061 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (274183232637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_52 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82286634115701 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193469839693 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨52, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82286634115701 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193469839693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_53 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82252992030319 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193473883269 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨53, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82252992030319 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193473883269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_54 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16443874620203 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193477929221 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨54, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16443874620203 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193477929221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_55 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (10273222162503 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096740957323 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨55, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (10273222162503 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096740957323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_56 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (3286088183989 / 4000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096742976923 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨56, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (3286088183989 / 4000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096742976923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_57 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8211865497263 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193489983527 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨57, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8211865497263 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193489983527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_58 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8208512839139 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193493999309 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨58, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8208512839139 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193493999309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_59 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8205162482879 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193497996611 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨59, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8205162482879 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193497996611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13204_40 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82692141860319 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193311698939 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨40, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82692141860319 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193311698939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_41 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82658219691127 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193315730969 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨41, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82658219691127 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193315730969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_42 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20656080255559 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193319735411 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨42, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20656080255559 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193319735411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_43 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82590445824159 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548330942463 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨43, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82590445824159 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548330942463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_44 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (2063914851689 / 2500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096663886989 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨44, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (2063914851689 / 2500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096663886989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_45 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (5157672857703 / 6250000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193331804987 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨45, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (5157672857703 / 6250000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193331804987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_46 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82488960762181 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193335802087 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨46, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82488960762181 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193335802087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_47 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82455179155461 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193339822093 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨47, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82455179155461 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193339822093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_48 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41210710437167 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548335965681 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨48, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41210710437167 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548335965681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_49 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82387685890193 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193347862471 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨49, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82387685890193 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193347862471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_50 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20588493543643 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438670375517 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨50, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20588493543643 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438670375517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_51 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82320285699147 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096677952573 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨51, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82320285699147 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096677952573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_52 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82286620435737 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (109667997101 / 5000000000000 : ℝ))
      (E := (cell13204 ⟨52, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82286620435737 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (109667997101 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_53 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (822529783563 / 1000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193363984867 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨53, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (822529783563 / 1000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193363984867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_54 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (16443871886587 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096683985507 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨54, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (16443871886587 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096683985507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_55 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (2054644090947 / 2500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096686007463 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨55, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (2054644090947 / 2500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096686007463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_56 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (10269023867939 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438675210707 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨56, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (10269023867939 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438675210707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_57 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82118641322343 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193380023477 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨57, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82118641322343 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193380023477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_58 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82085114747023 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548346024489 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨58, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82085114747023 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548346024489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_59 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (4102580559517 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438677618961 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨59, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (4102580559517 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438677618961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13205_40 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (10336516013841 / 12500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438640361893 / 20000000000000 : ℝ))
      (E := (cell13205 ⟨40, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (10336516013841 / 12500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438640361893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_41 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41329102973769 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438641156279 / 20000000000000 : ℝ))
      (E := (cell13205 ⟨41, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41329102973769 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438641156279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_42 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82624307284643 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096604921711 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨42, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82624307284643 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096604921711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_43 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82590432092559 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193213817809 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨43, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82590432092559 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193213817809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_44 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82556580341947 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096608939829 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨44, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82556580341947 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096608939829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_45 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82522752003617 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193221909571 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨45, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82522752003617 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193221909571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_46 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5155559190533 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109661295281 / 5000000000000 : ℝ))
      (E := (cell13205 ⟨46, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5155559190533 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109661295281 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_47 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (4122758272389 / 5000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137076870289 / 6250000000000 : ℝ))
      (E := (cell13205 ⟨47, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (4122758272389 / 5000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137076870289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_48 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82421407172621 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (274154245537 / 12500000000000 : ℝ))
      (E := (cell13205 ⟨48, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82421407172621 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (274154245537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_49 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82387672194443 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548309490783 / 25000000000000 : ℝ))
      (E := (cell13205 ⟨49, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82387672194443 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (548309490783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_50 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (4117698024239 / 5000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109662098869 / 5000000000000 : ℝ))
      (E := (cell13205 ⟨50, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (4117698024239 / 5000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109662098869 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_51 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82320272015309 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193246004121 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨51, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82320272015309 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193246004121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_52 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82286606757847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096625020111 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨52, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82286606757847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096625020111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_53 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41126482342177 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096627041171 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨53, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41126482342177 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096627041171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_54 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5138709110433 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193258067807 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨54, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5138709110433 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193258067807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_55 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5136609373613 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193262111083 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨55, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5136609373613 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193262111083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_56 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82152177289369 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193266149103 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨56, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82152177289369 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193266149103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_57 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (656949021393 / 800000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193270118501 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨57, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (656949021393 / 800000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193270118501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_58 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41042550552363 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096637096241 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨58, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41042550552363 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096637096241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_59 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82051597553959 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096639094439 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨59, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82051597553959 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096639094439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13206_40 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82692114363221 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096545957927 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨40, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82692114363221 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096545957927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_41 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82658192206033 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096547972661 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨41, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82658192206033 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096547972661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_42 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41312146774567 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193099947297 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨42, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41312146774567 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193099947297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_43 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82590418363041 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096551989681 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨43, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82590418363041 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096551989681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_44 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16511313323683 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548276995301 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨44, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16511313323683 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548276995301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_45 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82522738286067 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096556005011 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨45, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82522738286067 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096556005011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_46 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41244466668477 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096558002511 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨46, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41244466668477 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096558002511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_47 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41227575871089 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193120023023 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨47, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41227575871089 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193120023023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_48 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41210696736493 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096562030869 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨48, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41210696736493 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096562030869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_49 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (8238765850077 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193128059663 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨49, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (8238765850077 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193128059663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_50 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (10294243349633 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193132132077 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨50, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (10294243349633 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193132132077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_51 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16464051666709 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193136098969 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨51, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16464051666709 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193136098969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_52 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82286593082031 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193140134297 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨52, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82286593082031 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193140134297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_53 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82252951014481 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219314417569 / 10000000000000 : ℝ))
      (E := (cell13206 ⟨53, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82252951014481 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219314417569 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_54 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41109666051497 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096574080237 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨54, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41109666051497 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096574080237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_55 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82185736319807 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (438630440623 / 20000000000000 : ℝ))
      (E := (cell13206 ⟨55, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82185736319807 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (438630440623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_56 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82152163637297 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193156240547 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨56, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82152163637297 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193156240547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_57 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82118614027977 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193160268597 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨57, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82118614027977 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193160268597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_58 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41042543732249 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096582141443 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨58, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41042543732249 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096582141443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_59 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16410316783929 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (137073017427 / 6250000000000 : ℝ))
      (E := (cell13206 ⟨59, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16410316783929 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (137073017427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13207_40 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82692100617799 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548245504527 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨40, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82692100617799 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548245504527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_41 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82658178466611 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192986046297 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨41, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82658178466611 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192986046297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_42 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82624279815707 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192990047039 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨42, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82624279815707 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192990047039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_43 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20647601158901 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096497038959 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨43, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20647601158901 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096497038959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_44 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20639138224241 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548249534377 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨44, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20639138224241 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548249534377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_45 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20630681142649 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193002106343 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨45, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20630681142649 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193002106343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_46 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82488919627459 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193006159231 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨46, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82488919627459 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193006159231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_47 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82455138038653 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193010176253 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨47, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82455138038653 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193010176253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_48 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20605344943857 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438602842807 / 20000000000000 : ℝ))
      (E := (cell13207 ⟨48, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20605344943857 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438602842807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_49 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82387644809173 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193018211073 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨49, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82387644809173 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193018211073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_50 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (643390102433 / 781250000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (8566493061 / 390625000000 : ℝ))
      (E := (cell13207 ⟨50, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (643390102433 / 781250000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (8566493061 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_51 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (2572507645433 / 3125000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274128281093 / 12500000000000 : ℝ))
      (E := (cell13207 ⟨51, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (2572507645433 / 3125000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274128281093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_52 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82286579408289 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548257570831 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨52, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82286579408289 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548257570831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_53 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82252937346681 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438606864803 / 20000000000000 : ℝ))
      (E := (cell13207 ⟨53, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82252937346681 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438606864803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_54 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82219318441131 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193038308143 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨54, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82219318441131 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193038308143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_55 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82185722663877 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193042350173 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨55, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82185722663877 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193042350173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_56 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (16430429997459 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (13706539919 / 625000000000 : ℝ))
      (E := (cell13207 ⟨56, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (16430429997459 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (13706539919 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_57 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41059300191949 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193050414571 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨57, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41059300191949 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193050414571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_58 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82085073826337 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548263607097 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨58, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82085073826337 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548263607097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_59 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82051570287399 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193058423907 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨59, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82051570287399 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2193058423907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13208_40 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82692086874461 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (137054510939 / 6250000000000 : ℝ))
      (E := (cell13208 ⟨40, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82692086874461 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (137054510939 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_41 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (10332270591159 / 12500000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096438100979 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨41, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (10332270591159 / 12500000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096438100979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_42 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82624266084363 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192880201491 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨42, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82624266084363 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192880201491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_43 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82590390910249 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274110528901 / 12500000000000 : ℝ))
      (E := (cell13208 ⟨43, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82590390910249 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274110528901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_44 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82556539177593 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192888230793 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨44, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82556539177593 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192888230793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_45 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (16504542171441 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096446128723 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨45, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (16504542171441 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096446128723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_46 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41244452960021 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192896309311 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨46, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41244452960021 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192896309311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_47 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82455124337207 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096450162677 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨47, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82455124337207 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096450162677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_48 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41210683039973 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438580872441 / 20000000000000 : ℝ))
      (E := (cell13208 ⟨48, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41210683039973 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438580872441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_49 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20596907779913 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192908358357 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨49, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20596907779913 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192908358357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_50 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41176959713929 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192912370061 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨50, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41176959713929 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192912370061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_51 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82320230976241 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438583278879 / 20000000000000 : ℝ))
      (E := (cell13208 ⟨51, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82320230976241 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438583278879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_52 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (4114328286831 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192920428227 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨52, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (4114328286831 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192920428227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_53 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82252923680953 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192924468217 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨53, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82252923680953 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192924468217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_54 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (4110965239067 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274116056461 / 12500000000000 : ℝ))
      (E := (cell13208 ⟨54, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (4110965239067 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (274116056461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_55 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82185709010017 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219293249311 / 10000000000000 : ℝ))
      (E := (cell13208 ⟨55, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82185709010017 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (219293249311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_56 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41076068169681 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192936529413 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨56, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41076068169681 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192936529413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_57 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (641551458921 / 781250000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096470278213 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨57, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (641551458921 / 781250000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096470278213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_58 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (16417012038049 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192944569771 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨58, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (16417012038049 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192944569771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_59 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82051556657219 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (17132410663 / 781250000000 : ℝ))
      (E := (cell13208 ⟨59, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82051556657219 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (17132410663 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13209_40 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82692073133207 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096381163903 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨40, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82692073133207 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096381163903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_41 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (2583067218563 / 3125000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192766353487 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨41, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (2583067218563 / 3125000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192766353487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_42 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (826242523551 / 1000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096385205327 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨42, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (826242523551 / 1000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096385205327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_43 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41295188593487 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (137048398773 / 6250000000000 : ℝ))
      (E := (cell13209 ⟨43, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41295188593487 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (137048398773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_44 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41278262730151 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096389218863 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨44, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41278262730151 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096389218863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_45 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82522697145893 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096391231667 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨45, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82522697145893 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096391231667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_46 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (5155555763419 / 6250000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192786455263 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨46, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (5155555763419 / 6250000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192786455263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_47 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82455110637837 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219279047033 / 10000000000000 : ℝ))
      (E := (cell13209 ⟨47, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82455110637837 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219279047033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_48 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82421352386541 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192794506249 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨48, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82421352386541 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192794506249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_49 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41193808716103 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192798560523 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨49, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41193808716103 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192798560523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_50 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41176952873183 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548200642853 / 25000000000000 : ℝ))
      (E := (cell13209 ⟨50, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41176952873183 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (548200642853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_51 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (823202173007 / 1000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (68525206093 / 3125000000000 : ℝ))
      (E := (cell13209 ⟨51, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (823202173007 / 1000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (68525206093 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_52 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82286552067023 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192810569009 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨52, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82286552067023 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192810569009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_53 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82252910017297 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192814608297 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨53, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82252910017297 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192814608297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_54 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82219291123619 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096409325119 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨54, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82219291123619 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096409325119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_55 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82185695358227 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096411345537 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨55, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82185695358227 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096411345537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_56 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41076061346749 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192826667667 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨56, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41076061346749 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192826667667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_57 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41059286550973 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192830694163 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨57, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41059286550973 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192830694163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_58 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82085046556219 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192834707037 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨58, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82085046556219 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192834707037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_59 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41025771514553 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096419380473 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨59, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41025771514553 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096419380473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13210_40 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (20673014848509 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192652535251 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨40, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (20673014848509 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192652535251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_41 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41329068630421 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096328279851 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨41, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41329068630421 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096328279851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_42 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41312119313959 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (438532111369 / 20000000000000 : ℝ))
      (E := (cell13210 ⟨42, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41312119313959 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (438532111369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_43 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (4129518173289 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192664584263 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨43, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (4129518173289 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192664584263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_44 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (8255651174509 / 10000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192668640531 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨44, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (8255651174509 / 10000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192668640531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_45 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82522683436659 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096336332547 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨45, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82522683436659 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096336332547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_46 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82488878511443 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192676656023 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨46, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82488878511443 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192676656023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_47 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16491019388109 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192680670137 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨47, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16491019388109 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192680670137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_48 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (20605334673803 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (43853694103 / 2000000000000 : ℝ))
      (E := (cell13210 ⟨48, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (20605334673803 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (43853694103 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_49 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16477520749367 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192688699557 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨49, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16477520749367 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192688699557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_50 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82353892066949 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096346384319 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨50, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82353892066949 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096346384319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_51 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82320203627231 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096348395717 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨51, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82320203627231 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096348395717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_52 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82286538399499 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192700764743 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨52, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82286538399499 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192700764743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_53 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (642600752779 / 781250000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548176200839 / 25000000000000 : ℝ))
      (E := (cell13210 ⟨53, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (642600752779 / 781250000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548176200839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_54 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82219277467969 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096354422333 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨54, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82219277467969 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096354422333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_55 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82185681708507 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219271282577 / 10000000000000 : ℝ))
      (E := (cell13210 ⟨55, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82185681708507 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (219271282577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_56 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82152109049703 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548179215243 / 25000000000000 : ℝ))
      (E := (cell13210 ⟨56, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82152109049703 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548179215243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_57 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82118559464071 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (34261263859 / 1562500000000 : ℝ))
      (E := (cell13210 ⟨57, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82118559464071 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (34261263859 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_58 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82085032924261 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192724899403 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨58, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82085032924261 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192724899403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_59 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82051529403059 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192728952911 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨59, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82051529403059 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192728952911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13211_40 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82692045656947 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096271369283 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨40, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82692045656947 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096271369283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_41 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82658123529749 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192546761789 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨41, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82658123529749 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192546761789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_42 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82624224902817 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548137689437 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨42, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82624224902817 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548137689437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_43 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41295174873333 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (219255478403 / 10000000000000 : ℝ))
      (E := (cell13211 ⟨43, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41295174873333 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (219255478403 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_44 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41278249015979 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274069854901 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨44, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41278249015979 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274069854901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_45 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82522669729503 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192562862727 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨45, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82522669729503 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192562862727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_46 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82488864810259 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192566852659 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨46, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82488864810259 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192566852659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_47 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (5153442702833 / 6250000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192570865821 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨47, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (5153442702833 / 6250000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192570865821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_48 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82421325005957 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274071862491 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨48, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82421325005957 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274071862491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_49 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41193795031769 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096289476241 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨49, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41193795031769 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096289476241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_50 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16470775677921 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096291480871 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨50, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16470775677921 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096291480871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_51 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16464037991167 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192586983771 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨51, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16464037991167 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192586983771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_52 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41143262367023 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548147753859 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨52, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41143262367023 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548147753859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_53 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41126441348099 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438518998859 / 20000000000000 : ℝ))
      (E := (cell13211 ⟨53, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41126441348099 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (438518998859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_54 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (20554815953597 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (68518719843 / 3125000000000 : ℝ))
      (E := (cell13211 ⟨54, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (20554815953597 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (68518719843 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_55 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (10273208507607 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192603074643 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨55, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (10273208507607 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192603074643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_56 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (10269011925997 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548151777333 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨56, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (10269011925997 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548151777333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_57 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (10264818228533 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192611134867 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨57, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (10264818228533 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192611134867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_58 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (2565156852949 / 3125000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274076893359 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨58, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (2565156852949 / 3125000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274076893359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_59 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82051515779077 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096309570381 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨59, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82051515779077 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096309570381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13212_40 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (4134601596097 / 5000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192432996547 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨40, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (4134601596097 / 5000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192432996547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_41 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41329054900369 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438487403713 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨41, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41329054900369 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438487403713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_42 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82624211179797 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096220506683 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨42, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82624211179797 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096220506683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_43 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82590336029631 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274055629817 / 12500000000000 : ℝ))
      (E := (cell13212 ⟨43, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82590336029631 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274055629817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_44 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (10319560540113 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096224516879 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨44, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (10319560540113 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096224516879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_45 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (3300906240977 / 4000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096226528117 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨45, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (3300906240977 / 4000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096226528117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_46 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (5155553194447 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438491420821 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨46, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (5155553194447 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438491420821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_47 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82455069552187 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109623055817 / 5000000000000 : ℝ))
      (E := (cell13212 ⟨47, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82455069552187 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109623055817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_48 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41210655659389 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438493029913 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨48, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41210655659389 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438493029913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_49 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (20596894095579 / 25000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192469142277 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨49, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (20596894095579 / 25000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192469142277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_50 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41176932357167 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438494641951 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨50, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41176932357167 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438494641951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_51 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (5145011017907 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192477231039 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨51, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (5145011017907 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192477231039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_52 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16457302214133 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219248120293 / 10000000000000 : ℝ))
      (E := (cell13212 ⟨52, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16457302214133 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219248120293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_53 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41126434519377 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274060655027 / 12500000000000 : ℝ))
      (E := (cell13212 ⟨53, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41126434519377 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274060655027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_54 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82219250162877 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548122320073 / 25000000000000 : ℝ))
      (E := (cell13212 ⟨54, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82219250162877 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548122320073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_55 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82185654415273 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (10962466597 / 500000000000 : ℝ))
      (E := (cell13212 ⟨55, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82185654415273 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (10962466597 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_56 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82152081768317 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192497294403 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨56, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82152081768317 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192497294403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_57 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82118532194523 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274062664931 / 12500000000000 : ℝ))
      (E := (cell13212 ⟨57, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82118532194523 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (274062664931 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_58 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41042502833271 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (34257895797 / 1562500000000 : ℝ))
      (E := (cell13212 ⟨58, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41042502833271 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (34257895797 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_59 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (2051287553929 / 2500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109625469187 / 5000000000000 : ℝ))
      (E := (cell13212 ⟨59, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (2051287553929 / 2500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (109625469187 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13213_40 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (16538403637803 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096161625199 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨40, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (16538403637803 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096161625199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_41 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82658096073807 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096163606197 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨41, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82658096073807 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096163606197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_42 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (10328024682357 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274041408107 / 12500000000000 : ℝ))
      (E := (cell13213 ⟨42, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (10328024682357 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274041408107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_43 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (3303612892587 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438467057783 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨43, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (3303612892587 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438467057783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_44 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (10319558826491 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (17127650649 / 781250000000 : ℝ))
      (E := (cell13213 ⟨44, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (10319558826491 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (17127650649 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_45 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (5157665145089 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192343304529 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨45, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (5157665145089 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192343304529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_46 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82488837414121 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548086837857 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨46, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82488837414121 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548086837857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_47 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41227527930561 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438470272547 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨47, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41227527930561 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438470272547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_48 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82421297633673 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (54808884877 / 2500000000000 : ℝ))
      (E := (cell13213 ⟨48, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82421297633673 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (54808884877 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_49 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41193781351583 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096179693479 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨49, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41193781351583 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096179693479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_50 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (5147115690071 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192363453647 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨50, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (5147115690071 / 6250000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192363453647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_51 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82320162619259 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219236747419 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨51, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82320162619259 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219236747419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_52 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41143248704677 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274046430673 / 12500000000000 : ℝ))
      (E := (cell13213 ⟨52, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41143248704677 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274046430673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_53 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (4112642769169 / 5000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096187741009 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨53, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (4112642769169 / 5000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096187741009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_54 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (16443847302687 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219237952149 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨54, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (16443847302687 / 20000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219237952149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_55 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41092820385879 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (54809589001 / 2500000000000 : ℝ))
      (E := (cell13213 ⟨55, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41092820385879 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (54809589001 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_56 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (3286082725229 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219238753453 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨56, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (3286082725229 / 4000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219238753453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_57 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82118518562849 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548097889777 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨57, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82118518562849 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548097889777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_58 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82084992040781 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096197814733 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨58, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82084992040781 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096197814733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_59 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82051488537307 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096199811303 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨59, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82051488537307 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096199811303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13214_40 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82692004458171 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192213500121 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨40, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82692004458171 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192213500121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_41 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82658082348957 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192217519733 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨41, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82658082348957 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192217519733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_42 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41312091869997 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (109611075611 / 5000000000000 : ℝ))
      (E := (cell13214 ⟨42, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41312091869997 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (109611075611 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_43 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82590308601797 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (34253523987 / 1562500000000 : ℝ))
      (E := (cell13214 ⟨43, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82590308601797 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (34253523987 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_44 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82556456905029 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192229587151 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨44, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82556456905029 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192229587151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_45 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (165045257241 / 200000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192233607613 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨45, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (165045257241 / 200000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192233607613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_46 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41244411859583 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096118797313 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨46, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41244411859583 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096118797313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_47 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82455042172131 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (137015100313 / 6250000000000 : ℝ))
      (E := (cell13214 ⟨47, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82455042172131 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (137015100313 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_48 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41210641975321 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192245636473 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨48, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41210641975321 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192245636473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_49 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (8238754902609 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (548062421631 / 25000000000000 : ℝ))
      (E := (cell13214 ⟨49, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (8238754902609 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (548062421631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_50 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (8235383737001 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096126846709 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨50, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (8235383737001 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096126846709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_51 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82320148954079 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192257713219 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨51, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82320148954079 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192257713219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_52 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41143241875057 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438452348559 / 20000000000000 : ℝ))
      (E := (cell13214 ⟨52, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41143241875057 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438452348559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_53 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (20563210432519 / 25000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192265778803 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨53, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (20563210432519 / 25000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192265778803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_54 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41109611433031 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192269758571 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨54, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41109611433031 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192269758571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_55 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82185627130311 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192273796563 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨55, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82185627130311 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192273796563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_56 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82152054495199 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192277829713 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨56, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82152054495199 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192277829713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_57 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (2052962623331 / 2500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192281853849 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨57, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (2052962623331 / 2500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192281853849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_58 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16416995683417 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192285864591 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨58, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16416995683417 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192285864591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_59 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41025737459759 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (10961449583 / 500000000000 : ℝ))
      (E := (cell13214 ⟨59, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41025737459759 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (10961449583 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13215_40 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (1292062355147 / 1562500000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192103745717 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨40, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (1292062355147 / 1562500000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192103745717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_41 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82658068626187 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096053911473 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨41, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82658068626187 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096053911473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_42 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20656042505803 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192111814301 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨42, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20656042505803 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192111814301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_43 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41295147445499 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192115836163 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨43, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41295147445499 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192115836163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_44 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82556443200207 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192119828217 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨44, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82556443200207 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192119828217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_45 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82522614921651 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096061923831 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨45, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82522614921651 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096061923831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_46 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41244405013143 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192127892641 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨46, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41244405013143 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192127892641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_47 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16491005697043 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (54803297553 / 2500000000000 : ℝ))
      (E := (cell13215 ⟨47, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16491005697043 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (54803297553 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_48 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20605317567421 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192135932731 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨48, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20605317567421 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192135932731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_49 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41193767675543 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548034995493 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨49, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41193767675543 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548034995493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_50 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16470764740191 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192143988103 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨50, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16470764740191 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192143988103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_51 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (10290016911371 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192148007187 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨51, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (10290016911371 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192148007187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_52 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82286470092943 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192152036091 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨52, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82286470092943 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192152036091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_53 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (2056320701971 / 2500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096078035737 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨53, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (2056320701971 / 2500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096078035737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_54 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20554802305189 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096080025331 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨54, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20554802305189 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096080025331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_55 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82185613490931 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192164088121 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨55, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82185613490931 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192164088121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_56 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (4107602043087 / 5000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (137010507549 / 6250000000000 : ℝ))
      (E := (cell13215 ⟨56, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (4107602043087 / 5000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (137010507549 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_57 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82118491305697 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096086072239 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨57, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82118491305697 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096086072239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_58 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82084964795453 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (87687046193 / 4000000000000 : ℝ))
      (E := (cell13215 ⟨58, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82084964795453 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (87687046193 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_59 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82051461303793 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548045051621 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨59, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82051461303793 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548045051621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13216_40 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (3307679080109 / 4000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095997052389 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨40, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (3307679080109 / 4000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095997052389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_41 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16531610981099 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438399624407 / 20000000000000 : ℝ))
      (E := (cell13216 ⟨41, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16531610981099 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438399624407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_42 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82624156308507 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192002112259 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨42, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82624156308507 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192002112259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_43 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (3303611247291 / 4000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548001533259 / 25000000000000 : ℝ))
      (E := (cell13216 ⟨43, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (3303611247291 / 4000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548001533259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_44 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41278214748731 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109600509147 / 5000000000000 : ℝ))
      (E := (cell13216 ⟨44, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41278214748731 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109600509147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_45 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41261300612439 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438402840283 / 20000000000000 : ℝ))
      (E := (cell13216 ⟨45, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41261300612439 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438402840283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_46 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82488796335481 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192018186533 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨46, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82488796335481 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192018186533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_47 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (20613753700093 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192022195113 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨47, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (20613753700093 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192022195113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_48 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (206053141477 / 250000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192026224867 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨48, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (206053141477 / 250000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192026224867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_49 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16477504335631 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (21920302733 / 1000000000000 : ℝ))
      (E := (cell13216 ⟨49, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16477504335631 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (21920302733 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_50 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (20588452508493 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192034278669 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨50, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (20588452508493 / 25000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192034278669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_51 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (10290015203741 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548009574259 / 25000000000000 : ℝ))
      (E := (cell13216 ⟨51, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (10290015203741 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548009574259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_52 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41143228218921 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (219204232527 / 10000000000000 : ℝ))
      (E := (cell13216 ⟨52, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41143228218921 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (219204232527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_53 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82252814429673 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192046360029 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨53, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82252814429673 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192046360029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_54 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41109597788759 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192050397763 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨54, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41109597788759 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192050397763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_55 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41092799926809 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548013593891 / 25000000000000 : ℝ))
      (E := (cell13216 ⟨55, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41092799926809 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (548013593891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_56 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82152027230347 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109602920387 / 5000000000000 : ℝ))
      (E := (cell13216 ⟨56, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82152027230347 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (109602920387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_57 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82118477680219 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1096031215497 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨57, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82118477680219 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1096031215497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_58 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16416990235177 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192066440947 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨58, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16416990235177 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192066440947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_59 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82051447690131 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192070492257 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨59, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82051447690131 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2192070492257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13217_40 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82691963278121 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (54797110023 / 2500000000000 : ℝ))
      (E := (cell13217 ⟨40, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82691963278121 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (54797110023 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_41 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82658041186883 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191888416999 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨41, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82658041186883 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191888416999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_42 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82624142595881 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438378492987 / 20000000000000 : ℝ))
      (E := (cell13217 ⟨42, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82624142595881 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438378492987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_43 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8259026747563 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191896484651 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨43, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8259026747563 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191896484651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_44 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82556415796793 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (43838009493 / 2000000000000 : ℝ))
      (E := (cell13217 ⟨44, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82556415796793 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (43838009493 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_45 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82522587530181 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191904492133 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨45, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82522587530181 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191904492133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_46 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (329955130587 / 400000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095954267621 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨46, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (329955130587 / 400000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095954267621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_47 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82455001117603 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095956271473 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨47, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82455001117603 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095956271473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_48 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82421242913987 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191916571871 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨48, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82421242913987 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191916571871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_49 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16477501601459 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095960309759 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨49, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16477501601459 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095960309759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_50 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82353796369059 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191924624149 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨50, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82353796369059 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191924624149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_51 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41160053985479 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (68497770057 / 3125000000000 : ℝ))
      (E := (cell13217 ⟨51, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41160053985479 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (68497770057 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_52 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8228644278481 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547983167353 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨52, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8228644278481 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547983167353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_53 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82252800782573 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191936703571 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨53, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82252800782573 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191936703571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_54 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20554795484087 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (17535525453 / 800000000000 : ℝ))
      (E := (cell13217 ⟨54, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20554795484087 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (17535525453 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_55 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8218558621837 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547986179511 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨55, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8218558621837 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547986179511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_56 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41076006800509 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095974374879 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨56, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41076006800509 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095974374879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_57 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16423692811361 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438390554519 / 20000000000000 : ℝ))
      (E := (cell13217 ⟨57, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16423692811361 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438390554519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_58 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82084937558381 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191956782177 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨58, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82084937558381 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191956782177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_59 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20512858519633 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191960833163 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨59, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20512858519633 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191960833163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13218_40 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82691949555597 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (547943687933 / 25000000000000 : ℝ))
      (E := (cell13218 ⟨40, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82691949555597 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (547943687933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_41 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82658027470349 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095889383329 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨41, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82658027470349 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095889383329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_42 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (20656032221333 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (136986425843 / 6250000000000 : ℝ))
      (E := (cell13218 ⟨42, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (20656032221333 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (136986425843 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_43 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82590253771061 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (136986677009 / 6250000000000 : ℝ))
      (E := (cell13218 ⟨43, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82590253771061 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (136986677009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_44 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (412782010491 / 500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191790821129 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨44, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (412782010491 / 500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191790821129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_45 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41261286918779 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438358967529 / 20000000000000 : ℝ))
      (E := (cell13218 ⟨45, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41261286918779 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438358967529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_46 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82488768960093 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273974859979 / 12500000000000 : ℝ))
      (E := (cell13218 ⟨46, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82488768960093 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273974859979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_47 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82454987436907 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (109590144333 / 5000000000000 : ℝ))
      (E := (cell13218 ⟨47, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82454987436907 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (109590144333 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_48 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82421229239247 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438361382951 / 20000000000000 : ℝ))
      (E := (cell13218 ⟨48, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82421229239247 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438361382951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_49 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16477498867701 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191810961621 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨49, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16477498867701 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191810961621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_50 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82353782706217 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191814965513 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨50, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82353782706217 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191814965513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_51 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82320094314057 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191818982497 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨51, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82320094314057 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191818982497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_52 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41143214566923 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191823009439 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨52, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41143214566923 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191823009439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_53 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41126393568771 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095913521499 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨53, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41126393568771 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095913521499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_54 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82219168297243 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (4383662041 / 200000000000 : ℝ))
      (E := (cell13218 ⟨54, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82219168297243 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (4383662041 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_55 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82185572585189 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191835056411 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨55, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82185572585189 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191835056411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_56 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16430399994751 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191839087663 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨56, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16430399994751 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191839087663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_57 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16423690087091 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438368622017 / 20000000000000 : ℝ))
      (E := (cell13218 ⟨57, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16423690087091 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (438368622017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_58 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82084923942939 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191847119299 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨58, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82084923942939 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191847119299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_59 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (16410284093799 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (54796279249 / 2500000000000 : ℝ))
      (E := (cell13218 ⟨59, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (16410284093799 / 20000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (54796279249 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13219_40 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82691935835151 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191665098421 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨40, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82691935835151 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191665098421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_41 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20664503438973 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191669112197 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨41, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20664503438973 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191669112197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_42 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (4131205758843 / 5000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (13697957237 / 625000000000 : ℝ))
      (E := (cell13219 ⟨42, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (4131205758843 / 5000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (13697957237 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_43 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82590240068569 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191677175517 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨43, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82590240068569 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191677175517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_44 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (41278194200841 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191681163489 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨44, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (41278194200841 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191681163489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_45 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82522560147009 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (34245081843 / 1562500000000 : ℝ))
      (E := (cell13219 ⟨45, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82522560147009 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (34245081843 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_46 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82488755275509 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136980576269 / 6250000000000 : ℝ))
      (E := (cell13219 ⟨46, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82488755275509 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136980576269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_47 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82454973758283 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191693226257 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨47, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82454973758283 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191693226257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_48 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (41210607783289 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547924313381 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨48, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (41210607783289 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547924313381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_49 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82387480671787 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095850649803 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨49, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82387480671787 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095850649803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_50 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20588442261361 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095852651381 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨50, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20588442261361 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095852651381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_51 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (3292803226369 / 4000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136981832441 / 6250000000000 : ℝ))
      (E := (cell13219 ⟨51, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (3292803226369 / 4000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (136981832441 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_52 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (1645728309699 / 2000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191713345353 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨52, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (1645728309699 / 2000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191713345353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_53 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82252773494577 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095858689157 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨53, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82252773494577 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095858689157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_54 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (16443830932041 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547930353597 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨54, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (16443830932041 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547930353597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_55 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82185558954073 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (273965681227 / 12500000000000 : ℝ))
      (E := (cell13219 ⟨55, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82185558954073 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (273965681227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_56 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20537996587139 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191729480631 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨56, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20537996587139 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191729480631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_57 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (10264804602021 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191733502663 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨57, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (10264804602021 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191733502663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_58 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (2052122758239 / 2500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191737511531 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨58, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (2052122758239 / 2500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191737511531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_59 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82051406861519 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191741502651 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨59, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82051406861519 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191741502651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13220_40 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (5168245132299 / 6250000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438311099957 / 20000000000000 : ℝ))
      (E := (cell13220 ⟨40, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (5168245132299 / 6250000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438311099957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_41 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41329000021757 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136972469527 / 6250000000000 : ℝ))
      (E := (cell13220 ⟨41, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41329000021757 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136972469527 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_42 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (322750396369 / 390625000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547890889269 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨42, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (322750396369 / 390625000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547890889269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_43 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (10323778296019 / 12500000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191567573637 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨43, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (10323778296019 / 12500000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191567573637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_44 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41278187353619 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191571560621 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨44, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41278187353619 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191571560621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_45 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16504509291707 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095787787613 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨45, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16504509291707 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095787787613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_46 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41244370796499 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191579615597 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨46, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41244370796499 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191579615597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_47 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82454960081731 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191583620699 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨47, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82454960081731 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191583620699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_48 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82421201895981 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191587647161 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨48, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82421201895981 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191587647161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_49 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82387467007139 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095795846243 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨49, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82387467007139 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095795846243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_50 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (4117687769337 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (219159569493 / 10000000000000 : ℝ))
      (E := (cell13220 ⟨50, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (4117687769337 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (219159569493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_51 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41160033503231 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547899927639 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨51, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41160033503231 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547899927639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_52 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82286401838121 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438320747247 / 20000000000000 : ℝ))
      (E := (cell13220 ⟨52, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82286401838121 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438320747247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_53 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82252759853679 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191607768621 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨53, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82252759853679 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191607768621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_54 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82219141025233 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095805902083 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨54, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82219141025233 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095805902083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_55 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82185545325021 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191615839113 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨55, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82185545325021 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191615839113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_56 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (4107598636271 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (27395247629 / 1250000000000 : ℝ))
      (E := (cell13220 ⟨56, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (4107598636271 / 5000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (27395247629 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_57 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (2566200724967 / 3125000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095811915969 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨57, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (2566200724967 / 3125000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095811915969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_58 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20521224179561 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273953487457 / 12500000000000 : ℝ))
      (E := (cell13220 ⟨58, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20521224179561 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273953487457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_59 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16410278651221 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191631890477 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨59, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16410278651221 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191631890477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13221_40 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (16538381680099 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191445897027 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨40, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (16538381680099 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191445897027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_41 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20664496583303 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547862477137 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨41, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20664496583303 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547862477137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_42 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (16524817553229 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191453952111 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨42, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (16524817553229 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191453952111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_43 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8259021266981 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191457967639 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨43, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8259021266981 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191457967639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_44 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82556361014869 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095730976817 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨44, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82556361014869 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095730976817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_45 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82522532772133 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095732983649 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨45, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82522532772133 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095732983649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_46 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82488727912559 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191470006773 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨46, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82488727912559 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191470006773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_47 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (329819785629 / 400000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095737005513 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨47, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (329819785629 / 400000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095737005513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_48 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82421188227453 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438295607337 / 20000000000000 : ℝ))
      (E := (cell13221 ⟨48, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82421188227453 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438295607337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_49 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (1029843166807 / 1250000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191482081251 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨49, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (1029843166807 / 1250000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191482081251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_50 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (16470748346021 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273935760373 / 12500000000000 : ℝ))
      (E := (cell13221 ⟨50, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (16470748346021 / 20000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273935760373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_51 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41160026677883 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438298019589 / 20000000000000 : ℝ))
      (E := (cell13221 ⟨51, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41160026677883 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438298019589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_52 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (1028579852417 / 1250000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191494123003 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨52, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (1028579852417 / 1250000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191494123003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_53 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82252746214847 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191498154817 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨53, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82252746214847 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191498154817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_54 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (3288765095693 / 4000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547875547459 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨54, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (3288765095693 / 4000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547875547459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_55 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41092765849017 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191506224299 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨55, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41092765849017 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191506224299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_56 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82151959104349 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191510254243 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨56, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82151959104349 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191510254243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_57 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82118409583783 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438302855099 / 20000000000000 : ℝ))
      (E := (cell13221 ⟨57, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82118409583783 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (438302855099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_58 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82084883108989 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095759141837 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨58, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82084883108989 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095759141837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_59 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82051379652751 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191522333441 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨59, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82051379652751 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191522333441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13222_40 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82691894686283 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191336290149 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨40, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82691894686283 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191336290149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_41 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41328986312493 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438268071873 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨41, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41328986312493 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438268071873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_42 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82624074063901 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547836085757 / 25000000000000 : ℝ))
      (E := (cell13222 ⟨42, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82624074063901 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (547836085757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_43 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41295099486771 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191348357523 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨43, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41295099486771 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191348357523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_44 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82556347324573 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191352401421 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨44, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82556347324573 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191352401421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_45 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20630629771951 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (273919551771 / 12500000000000 : ℝ))
      (E := (cell13222 ⟨45, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20630629771951 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (273919551771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_46 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82488714234193 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191360452771 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨46, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82488714234193 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191360452771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_47 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82454932734841 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095682228099 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨47, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82454932734841 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095682228099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_48 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20605293640249 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095684240539 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨48, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20605293640249 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095684240539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_49 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82387439684051 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191372524911 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨49, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82387439684051 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191372524911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_50 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82353728075539 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191376525957 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨50, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82353728075539 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191376525957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_51 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82320039707137 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191380540277 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨51, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82320039707137 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191380540277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_52 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16457274910133 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (109569228237 / 5000000000000 : ℝ))
      (E := (cell13222 ⟨52, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16457274910133 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (109569228237 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_53 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (514079578613 / 625000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438277719201 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨53, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (514079578613 / 625000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438277719201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_54 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82219113761483 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (54784815763 / 2500000000000 : ℝ))
      (E := (cell13222 ⟨54, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82219113761483 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (54784815763 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_55 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (8218551807311 / 10000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (136962291533 / 6250000000000 : ℝ))
      (E := (cell13222 ⟨55, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (8218551807311 / 10000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (136962291533 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_56 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (4107597274267 / 5000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (273925079361 / 12500000000000 : ℝ))
      (E := (cell13222 ⟨56, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (4107597274267 / 5000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (273925079361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_57 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20529598992671 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191404655751 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨57, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20529598992671 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191404655751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_58 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16416973900359 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191408722807 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨58, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16416973900359 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191408722807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_59 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82051366051457 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095706356529 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨59, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82051366051457 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095706356529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13223_40 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20672970243537 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547806684487 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨40, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20672970243537 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547806684487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_41 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20664489729709 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191230747243 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨41, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20664489729709 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191230747243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_42 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20656015090933 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191234788671 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨42, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20656015090933 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191234788671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_43 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82590185279349 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191238802157 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨43, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82590185279349 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191238802157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_44 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82556333636351 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547810711273 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨44, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82556333636351 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547810711273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_45 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20630626351387 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095623428461 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨45, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20630626351387 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095623428461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_46 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41244350278949 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438250178931 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨46, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41244350278949 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438250178931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_47 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41227459532251 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095627448629 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨47, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41227459532251 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095627448629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_48 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82421160896609 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191258921359 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨48, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82421160896609 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191258921359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_49 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (8238742602561 / 10000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (109563148223 / 5000000000000 : ℝ))
      (E := (cell13223 ⟨49, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (8238742602561 / 10000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (109563148223 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_50 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (64338839393 / 78125000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (109563348241 / 5000000000000 : ℝ))
      (E := (cell13223 ⟨50, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (64338839393 / 78125000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (109563348241 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_51 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (2572500814393 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191270978499 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨51, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (2572500814393 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191270978499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_52 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20571590227509 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (4279833989 / 195312500000 : ℝ))
      (E := (cell13223 ⟨52, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20571590227509 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (4279833989 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_53 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82252718943379 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438255806617 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨53, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82252718943379 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438255806617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_54 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (2569346879147 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095641533549 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨54, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (2569346879147 / 3125000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095641533549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_55 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (328742017801 / 400000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191287100649 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨55, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (328742017801 / 400000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191287100649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_56 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82151931868393 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (10956455353 / 500000000000 : ℝ))
      (E := (cell13223 ⟨56, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82151931868393 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (10956455353 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_57 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82118382359647 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191295150293 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨57, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82118382359647 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191295150293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_58 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82084855896661 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547824789459 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨58, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82084855896661 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547824789459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_59 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (641026191033 / 781250000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095651573907 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨59, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (641026191033 / 781250000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095651573907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13224_40 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82691867264089 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (219111718163 / 10000000000000 : ℝ))
      (E := (cell13224 ⟨40, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82691867264089 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (219111718163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_41 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41328972607381 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547780312161 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨41, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41328972607381 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547780312161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_42 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41312023332819 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191125230197 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨42, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41312023332819 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191125230197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_43 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82590171587229 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191129301543 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨43, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82590171587229 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191129301543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_44 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82556319950201 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191133284649 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨44, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82556319950201 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191133284649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_45 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20630622931341 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095568647781 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨45, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20630622931341 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095568647781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_46 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82488686883673 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095570666213 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨46, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82488686883673 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095570666213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_47 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82454905396233 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438229066841 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨47, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82454905396233 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438229066841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_48 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82421147234291 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191149357529 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨48, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82421147234291 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191149357529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_49 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41193706184619 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095576699949 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨49, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41193706184619 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095576699949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_50 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82353700772609 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547789349893 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨50, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82353700772609 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547789349893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_51 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82320012416081 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547790367917 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨51, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82320012416081 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547790367917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_52 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (5142896704467 / 6250000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191165494967 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨52, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (5142896704467 / 6250000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191165494967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_53 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41126352655371 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095584733029 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨53, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41126352655371 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095584733029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_54 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (8221908650599 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191173499569 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨54, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (8221908650599 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191173499569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_55 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82185490829453 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438235506533 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨55, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82185490829453 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438235506533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_56 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82151918253509 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095590780689 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨56, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82151918253509 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095590780689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_57 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (8211836875067 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191185581537 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨57, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (8211836875067 / 10000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191185581537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_58 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20521210573397 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191189588761 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨58, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20521210573397 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191189588761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_59 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82051338855049 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191193637711 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨59, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82051338855049 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191193637711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

end BstLean.Part268
