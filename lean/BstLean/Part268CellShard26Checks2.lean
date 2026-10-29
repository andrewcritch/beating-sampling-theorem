import BstLean.Part268CellShard26Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13000_40 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82694991064337 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216163919291 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨40, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82694991064337 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216163919291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_41 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82661067651429 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277020988709 / 12500000000000 : ℝ))
      (E := (cell13000 ⟨41, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82661067651429 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277020988709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_42 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82627167739839 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443234384293 / 20000000000000 : ℝ))
      (E := (cell13000 ⟨42, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82627167739839 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443234384293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_43 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82593291300079 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216175953463 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨43, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82593291300079 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216175953463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_44 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82559438302809 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (69255623293 / 3125000000000 : ℝ))
      (E := (cell13000 ⟨44, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82559438302809 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (69255623293 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_45 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20631402179709 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216183954387 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨45, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20631402179709 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216183954387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_46 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82491802519113 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216187978643 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨46, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82491802519113 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216187978643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_47 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82458019674739 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108095978569 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨47, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82458019674739 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108095978569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_48 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82424260156959 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216196005443 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨48, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82424260156959 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216196005443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_49 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (2059763098429 / 2500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443240000633 / 20000000000000 : ℝ))
      (E := (cell13000 ⟨49, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (2059763098429 / 2500000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (443240000633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_50 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41178405493437 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277025500817 / 12500000000000 : ℝ))
      (E := (cell13000 ⟨50, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41178405493437 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (277025500817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_51 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (3292924851111 / 4000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108104006319 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨51, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (3292924851111 / 4000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108104006319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_52 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82289454781677 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108106009173 / 50000000000000 : ℝ))
      (E := (cell13000 ⟨52, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82289454781677 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (1108106009173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_53 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82255811470537 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216216020319 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨53, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82255811470537 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216216020319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_54 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (1644443826329 / 2000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216220074119 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨54, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (1644443826329 / 2000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216220074119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_55 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (82188594291651 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554056014451 / 25000000000000 : ℝ))
      (E := (cell13000 ⟨55, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (82188594291651 / 100000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (554056014451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_56 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (641836096629 / 781250000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216228085647 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨56, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (641836096629 / 781250000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216228085647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_57 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41060734759773 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216232094373 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨57, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41060734759773 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216232094373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_58 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (41043970858699 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (221623607961 / 10000000000000 : ℝ))
      (E := (cell13000 ⟨58, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (41043970858699 / 50000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (221623607961 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13000_59 : CellCertificate 13000 (109811900457363 / 1250000000000000 : ℝ) (1615713025597887 / 1000000000000000000 : ℝ) (326187468107977 / 10000000000000000 : ℝ)
    (cell13000 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · norm_num [cell13000]
  · have h := gap_lower (n := 13000) (a := (20513609233713 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216240095999 / 100000000000000 : ℝ))
      (E := (cell13000 ⟨59, by decide⟩).energy) (xi := (326187468107977 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13000 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13000]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13000])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13000) (a := (20513609233713 / 25000000000000 : ℝ)) (b := (19800309223 / 12500000000000 : ℝ)) (q := (2216240095999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13000])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13000]

theorem cert13001_40 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (1292109013739 / 1562500000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108024831377 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨40, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (1292109013739 / 1562500000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108024831377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_41 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (4133052673629 / 5000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216053649591 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨41, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (4133052673629 / 5000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216053649591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_42 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82627153567177 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216057657887 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨42, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82627153567177 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216057657887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_43 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82593277133599 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443212337287 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨43, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82593277133599 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443212337287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_44 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41279712071253 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216065674943 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨44, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41279712071253 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216065674943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_45 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (16505118912941 / 20000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (69252179359 / 3125000000000 : ℝ))
      (E := (cell13001 ⟨45, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (16505118912941 / 20000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (69252179359 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_46 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20622947092787 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216073701539 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨46, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20622947092787 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216073701539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_47 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (10307250691617 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108038867853 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨47, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (10307250691617 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108038867853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_48 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82424246021313 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554020430463 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨48, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82424246021313 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554020430463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_49 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (41195254903833 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443217155077 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨49, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (41195254903833 / 50000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443217155077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_50 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82356796863527 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216089775651 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨50, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82356796863527 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216089775651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_51 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (8232310716057 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108046889347 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨51, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (8232310716057 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108046889347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_52 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82289440670609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554024445347 / 25000000000000 : ℝ))
      (E := (cell13001 ⟨52, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82289440670609 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (554024445347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_53 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82255797365601 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108050890197 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨53, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82255797365601 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108050890197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_54 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82222177217641 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (277013228909 / 12500000000000 : ℝ))
      (E := (cell13001 ⟨54, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82222177217641 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (277013228909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_55 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (20547145049741 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216109812083 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨55, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (20547145049741 / 25000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216109812083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_56 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (10269375785243 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443222767419 / 20000000000000 : ℝ))
      (E := (cell13001 ⟨56, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (10269375785243 / 12500000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (443222767419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_57 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (8212145543909 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216117843037 / 100000000000000 : ℝ))
      (E := (cell13001 ⟨57, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (8212145543909 / 10000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (2216117843037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_58 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (1641758552861 / 2000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108060942367 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨58, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (1641758552861 / 2000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108060942367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13001_59 : CellCertificate 13001 (878468492376237 / 10000000000000000 : ℝ) (1615588709625177 / 1000000000000000000 : ℝ) (326161794577759 / 10000000000000000 : ℝ)
    (cell13001 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · norm_num [cell13001]
  · have h := gap_lower (n := 13001) (a := (82054422866607 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108062949227 / 50000000000000 : ℝ))
      (E := (cell13001 ⟨59, by decide⟩).energy) (xi := (326161794577759 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13001 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13001]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13001])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13001) (a := (82054422866607 / 100000000000000 : ℝ)) (b := (79195074043 / 50000000000000 : ℝ)) (q := (1108062949227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13001])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13001]

theorem cert13002_40 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (2067374067411 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107967730323 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨40, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (2067374067411 / 2500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107967730323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_41 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (16532207859183 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443187888793 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨41, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (16532207859183 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443187888793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_42 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41313569698349 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553985862197 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨42, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41313569698349 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553985862197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_43 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82593262969301 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221594747391 / 10000000000000 : ℝ))
      (E := (cell13002 ⟨43, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82593262969301 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221594747391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_44 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (644995390503 / 781250000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215951459037 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨44, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (644995390503 / 781250000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215951459037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_45 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82525580412753 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276994440031 / 12500000000000 : ℝ))
      (E := (cell13002 ⟨45, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82525580412753 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276994440031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_46 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82491774225363 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221595947901 / 10000000000000 : ℝ))
      (E := (cell13002 ⟨46, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82491774225363 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (221595947901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_47 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82457991393311 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138497719371 / 6250000000000 : ℝ))
      (E := (cell13002 ⟨47, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82457991393311 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138497719371 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_48 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20606057971961 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276995943981 / 12500000000000 : ℝ))
      (E := (cell13002 ⟨48, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20606057971961 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (276995943981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_49 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20597623920087 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553992885817 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨49, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20597623920087 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553992885817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_50 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (16471356548471 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215975540429 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨50, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (16471356548471 / 20000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215975540429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_51 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82323093045539 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107989770207 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨51, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82323093045539 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1107989770207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_52 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41144713280857 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443196708019 / 20000000000000 : ℝ))
      (E := (cell13002 ⟨52, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41144713280857 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (443196708019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_53 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82255783262837 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138499224701 / 6250000000000 : ℝ))
      (E := (cell13002 ⟨53, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82255783262837 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (138499224701 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_54 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (20555540780251 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553997896023 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨54, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (20555540780251 / 25000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553997896023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_55 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (2568392690889 / 3125000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553998905289 / 25000000000000 : ℝ))
      (E := (cell13002 ⟨55, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (2568392690889 / 3125000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (553998905289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_56 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (10269374024693 / 12500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215999643363 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨56, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (10269374024693 / 12500000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2215999643363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_57 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (41060720680401 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1108001823273 / 50000000000000 : ℝ))
      (E := (cell13002 ⟨57, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (41060720680401 / 50000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (1108001823273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_58 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82087913570869 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2216007626331 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨58, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82087913570869 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2216007626331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13002_59 : CellCertificate 13002 (878441785029587 / 10000000000000000 : ℝ) (1615464412781199 / 1000000000000000000 : ℝ) (326136125123557 / 10000000000000000 : ℝ)
    (cell13002 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · norm_num [cell13002]
  · have h := gap_lower (n := 13002) (a := (82054408800529 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2216011637359 / 100000000000000 : ℝ))
      (E := (cell13002 ⟨59, by decide⟩).energy) (xi := (326136125123557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13002 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13002]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13002])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13002) (a := (82054408800529 / 100000000000000 : ℝ)) (b := (39594456079 / 25000000000000 : ℝ)) (q := (2216011637359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13002])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13002]

theorem cert13003_40 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82694948515769 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443164250839 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨40, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82694948515769 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443164250839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_41 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82661025121433 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107912616999 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨41, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82661025121433 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107912616999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_42 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82627125228401 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215829235349 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨42, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82627125228401 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215829235349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_43 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (5162078050449 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443166651409 / 20000000000000 : ℝ))
      (E := (cell13003 ⟨43, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (5162078050449 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (443166651409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_44 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41279697914221 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107918648831 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨44, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41279697914221 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107918648831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_45 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82525566262981 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215841296671 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨45, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82525566262981 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215841296671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_46 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16498352016351 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107922655531 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨46, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16498352016351 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107922655531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_47 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (10307247156983 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215849338769 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨47, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (10307247156983 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215849338769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_48 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82424217756551 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215853318547 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨48, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82424217756551 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215853318547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_49 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (16478096311041 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215857306817 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨49, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (16478096311041 / 20000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215857306817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_50 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41178384311679 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553965339971 / 25000000000000 : ℝ))
      (E := (cell13003 ⟨50, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41178384311679 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553965339971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_51 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82323078932681 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553966339209 / 25000000000000 : ℝ))
      (E := (cell13003 ⟨51, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82323078932681 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (553966339209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_52 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (5143088278437 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276983669191 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨52, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (5143088278437 / 6250000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276983669191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_53 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41127884581123 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107936702853 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨53, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41127884581123 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107936702853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_54 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82222149026537 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276984673961 / 12500000000000 : ℝ))
      (E := (cell13003 ⟨54, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82222149026537 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (276984673961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_55 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82188552020103 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215881425899 / 100000000000000 : ℝ))
      (E := (cell13003 ⟨55, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82188552020103 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (2215881425899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_56 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (41077489057657 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107942722651 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨56, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (41077489057657 / 50000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107942722651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_57 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82121427284683 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107944722863 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨57, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82121427284683 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107944722863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_58 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (10260987437607 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107946711399 / 50000000000000 : ℝ))
      (E := (cell13003 ⟨58, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (10260987437607 / 12500000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (1107946711399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13003_59 : CellCertificate 13003 (878415081618041 / 10000000000000000 : ℝ) (807670067530769 / 500000000000000000 : ℝ) (326110459744341 / 10000000000000000 : ℝ)
    (cell13003 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · norm_num [cell13003]
  · have h := gap_lower (n := 13003) (a := (82054394736617 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55397435779 / 2500000000000 : ℝ))
      (E := (cell13003 ⟨59, by decide⟩).energy) (xi := (326110459744341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13003 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13003]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13003])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13003) (a := (82054394736617 / 100000000000000 : ℝ)) (b := (158365502471 / 100000000000000 : ℝ)) (q := (55397435779 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13003])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13003]

theorem cert13004_40 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (64605417451 / 78125000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215707043403 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨40, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (64605417451 / 78125000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215707043403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_41 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41330505474567 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215711078487 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨41, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41330505474567 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215711078487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_42 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41313555531143 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215715076391 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨42, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41313555531143 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215715076391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_43 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82593234647249 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443143818937 / 20000000000000 : ℝ))
      (E := (cell13004 ⟨43, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82593234647249 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443143818937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_44 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (2063984541867 / 2500000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553930782987 / 25000000000000 : ℝ))
      (E := (cell13004 ⟨44, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (2063984541867 / 2500000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553930782987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_45 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (20631388028847 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215727127647 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨45, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (20631388028847 / 25000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215727127647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_46 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41245872970163 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (88629245551 / 4000000000000 : ℝ))
      (E := (cell13004 ⟨46, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41245872970163 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (88629245551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_47 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41228981560297 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443147032653 / 20000000000000 : ℝ))
      (E := (cell13004 ⟨47, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41228981560297 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443147032653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_48 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (16484840725487 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215739139871 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨48, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (16484840725487 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215739139871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_49 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41195233716119 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553935796001 / 25000000000000 : ℝ))
      (E := (cell13004 ⟨49, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41195233716119 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (553935796001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_50 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (16471350901307 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443149435001 / 20000000000000 : ℝ))
      (E := (cell13004 ⟨50, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (16471350901307 / 20000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (443149435001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_51 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82323064821997 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215751168923 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨51, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82323064821997 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215751168923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_52 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41144699175221 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107877610843 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨52, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41144699175221 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107877610843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_53 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (3290230202553 / 4000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107879605933 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨53, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (3290230202553 / 4000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107879605933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_54 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41111067467121 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44315263899 / 2000000000000 : ℝ))
      (E := (cell13004 ⟨54, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41111067467121 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (44315263899 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_55 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (41094268966963 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107883613157 / 50000000000000 : ℝ))
      (E := (cell13004 ⟨55, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (41094268966963 / 50000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (1107883613157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_56 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82154964035253 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (69242851341 / 3125000000000 : ℝ))
      (E := (cell13004 ⟨56, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82154964035253 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (69242851341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_57 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82121413210731 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215775240579 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨57, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82121413210731 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215775240579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_58 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (82087885433009 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215779274137 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨58, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (82087885433009 / 100000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215779274137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13004_59 : CellCertificate 13004 (54899273883793 / 625000000000000 : ℝ) (1615215876461781 / 1000000000000000000 : ℝ) (326084798439077 / 10000000000000000 : ℝ)
    (cell13004 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · norm_num [cell13004]
  · have h := gap_lower (n := 13004) (a := (8205438067487 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215783279857 / 100000000000000 : ℝ))
      (E := (cell13004 ⟨59, by decide⟩).energy) (xi := (326084798439077 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13004 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13004]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13004])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13004) (a := (8205438067487 / 10000000000000 : ℝ)) (b := (158353182553 / 100000000000000 : ℝ)) (q := (2215783279857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13004])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13004]

theorem cert13005_40 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (5168432510061 / 6250000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443118577409 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨40, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (5168432510061 / 6250000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443118577409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_41 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82660996779017 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215596918637 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨41, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82660996779017 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215596918637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_42 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82627096898353 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107800456547 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨42, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82627096898353 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107800456547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_43 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82593220489493 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553901231997 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨43, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82593220489493 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553901231997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_44 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41279683761549 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276951120237 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨44, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41279683761549 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276951120237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_45 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41262768984987 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215612954287 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨45, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41262768984987 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215612954287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_46 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (3299669272043 / 4000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215616962153 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨46, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (3299669272043 / 4000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215616962153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_47 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (6596635919 / 8000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215620983427 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨47, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (6596635919 / 8000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215620983427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_48 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16484837900099 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107812507913 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨48, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16484837900099 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107812507913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_49 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41195226655723 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215628997871 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨49, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41195226655723 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215628997871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_50 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16471348078377 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443126608961 / 20000000000000 : ℝ))
      (E := (cell13005 ⟨50, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16471348078377 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (443126608961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_51 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (41161525356743 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107818517857 / 50000000000000 : ℝ))
      (E := (cell13005 ⟨51, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (41161525356743 / 50000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (1107818517857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_52 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (16457876849613 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276955128307 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨52, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (16457876849613 / 20000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276955128307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_53 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (10281967620947 / 12500000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215645072777 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨53, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (10281967620947 / 12500000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215645072777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_54 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (20555530211029 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221564905299 / 10000000000000 : ℝ))
      (E := (cell13005 ⟨54, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (20555530211029 / 25000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (221564905299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_55 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82188523849919 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276956635191 / 12500000000000 : ℝ))
      (E := (cell13005 ⟨55, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82188523849919 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (276956635191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_56 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82154949957359 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553914273837 / 25000000000000 : ℝ))
      (E := (cell13005 ⟨56, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82154949957359 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (553914273837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_57 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82121399138947 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215661090281 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨57, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82121399138947 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215661090281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_58 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82087871367329 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (17309883759 / 781250000000 : ℝ))
      (E := (cell13005 ⟨58, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82087871367329 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (17309883759 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13005_59 : CellCertificate 13005 (109795210824577 / 1250000000000000 : ℝ) (403772909244379 / 250000000000000000 : ℝ) (326059141206737 / 10000000000000000 : ℝ)
    (cell13005 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · norm_num [cell13005]
  · have h := gap_lower (n := 13005) (a := (82054366615289 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215669124229 / 100000000000000 : ℝ))
      (E := (cell13005 ⟨59, by decide⟩).energy) (xi := (326059141206737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13005 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13005]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13005])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13005) (a := (82054366615289 / 100000000000000 : ℝ)) (b := (158340864559 / 100000000000000 : ℝ)) (q := (2215669124229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13005])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13005]

theorem cert13006_40 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82694905986853 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553869696281 / 25000000000000 : ℝ))
      (E := (cell13006 ⟨40, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82694905986853 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (553869696281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_41 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82660982611083 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107741406623 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨41, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82660982611083 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107741406623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_42 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (413135413683 / 500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107743402141 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨42, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (413135413683 / 500000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107743402141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_43 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82593206333917 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (11077454079 / 500000000000 : ℝ))
      (E := (cell13006 ⟨43, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82593206333917 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (11077454079 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_44 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41279676686847 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107747423189 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨44, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41279676686847 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107747423189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_45 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82525523826737 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443099767097 / 20000000000000 : ℝ))
      (E := (cell13006 ⟨45, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82525523826737 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (443099767097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_46 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (2577866177 / 3125000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215502840113 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨46, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (2577866177 / 3125000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215502840113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_47 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82457934856583 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107753429097 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨47, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82457934856583 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107753429097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_48 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82424175375729 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276938860931 / 12500000000000 : ℝ))
      (E := (cell13006 ⟨48, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82424175375729 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276938860931 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_49 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (20597609798207 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276939358299 / 12500000000000 : ℝ))
      (E := (cell13006 ⟨49, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (20597609798207 / 25000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (276939358299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_50 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82356726279409 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215518910273 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨50, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82356726279409 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215518910273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_51 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82323036607147 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107761449087 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨51, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82323036607147 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107761449087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_52 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41144685073929 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107763442977 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨52, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41144685073929 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107763442977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_53 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82255726873497 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107765464679 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨53, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82255726873497 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107765464679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_54 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82222106756159 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107767482903 / 50000000000000 : ℝ))
      (E := (cell13006 ⟨54, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82222106756159 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (1107767482903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_55 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (1027356372101 / 1250000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (34617795819 / 1562500000000 : ℝ))
      (E := (cell13006 ⟨55, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (1027356372101 / 1250000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (34617795819 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_56 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82154935881633 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215542943457 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨56, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82154935881633 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215542943457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_57 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82121385069329 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138471687177 / 6250000000000 : ℝ))
      (E := (cell13006 ⟨57, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82121385069329 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (138471687177 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_58 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (41043928651907 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215550963841 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨58, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (41043928651907 / 50000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215550963841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13006_59 : CellCertificate 13006 (439167497492457 / 5000000000000000 : ℝ) (403741854151083 / 250000000000000000 : ℝ) (326033488046287 / 10000000000000000 : ℝ)
    (cell13006 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · norm_num [cell13006]
  · have h := gap_lower (n := 13006) (a := (82054352557873 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215555023499 / 100000000000000 : ℝ))
      (E := (cell13006 ⟨59, by decide⟩).energy) (xi := (326033488046287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13006 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13006]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13006])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13006) (a := (82054352557873 / 100000000000000 : ℝ)) (b := (158328548491 / 100000000000000 : ℝ)) (q := (2215555023499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13006])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13006]

theorem cert13007_40 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82694891814913 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138460292429 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨40, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82694891814913 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138460292429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_41 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82660968445329 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215368703519 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨41, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82660968445329 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215368703519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_42 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (20656767144257 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553843172783 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨42, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (20656767144257 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553843172783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_43 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82593192180521 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553844174819 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨43, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82593192180521 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553844174819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_44 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82559339226469 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553845181631 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨44, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82559339226469 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553845181631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_45 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41262754842839 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553846178087 / 25000000000000 : ℝ))
      (E := (cell13007 ⟨45, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41262754842839 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (553846178087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_46 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41245851764551 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110769435687 / 5000000000000 : ℝ))
      (E := (cell13007 ⟨46, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41245851764551 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110769435687 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_47 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82457920727841 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (221539272863 / 10000000000000 : ℝ))
      (E := (cell13007 ⟨47, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82457920727841 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (221539272863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_48 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41212080626569 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215396754739 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨48, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41212080626569 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215396754739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_49 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82390425076383 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215400789571 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨49, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82390425076383 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215400789571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_50 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41178356084553 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215404771411 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨50, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41178356084553 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215404771411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_51 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (4116151125149 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215408815339 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨51, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (4116151125149 / 5000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215408815339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_52 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41144678024911 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107706400091 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨52, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41144678024911 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107706400091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_53 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82255712781587 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443083368139 / 20000000000000 : ℝ))
      (E := (cell13007 ⟨53, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82255712781587 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (443083368139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_54 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (20555523167593 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215420815191 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨54, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (20555523167593 / 25000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215420815191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_55 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82188495688409 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107712419053 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨55, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82188495688409 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107712419053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_56 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (41077460904037 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215428846393 / 100000000000000 : ℝ))
      (E := (cell13007 ⟨56, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (41077460904037 / 50000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (2215428846393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_57 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82121371001877 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110771644753 / 5000000000000 : ℝ))
      (E := (cell13007 ⟨57, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82121371001877 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (110771644753 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_58 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (16417568648493 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107718430703 / 50000000000000 : ℝ))
      (E := (cell13007 ⟨58, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (16417568648493 / 20000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (1107718430703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13007_59 : CellCertificate 13007 (878308307304669 / 10000000000000000 : ℝ) (80742160766891 / 50000000000000000 : ℝ) (326007838956699 / 10000000000000000 : ℝ)
    (cell13007 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · norm_num [cell13007]
  · have h := gap_lower (n := 13007) (a := (82054338502621 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138465057403 / 6250000000000 : ℝ))
      (E := (cell13007 ⟨59, by decide⟩).energy) (xi := (326007838956699 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13007 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13007]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13007])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13007) (a := (82054338502621 / 100000000000000 : ℝ)) (b := (79158117173 / 50000000000000 : ℝ)) (q := (138465057403 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13007])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13007]

theorem cert13008_40 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16538975529031 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443050113653 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨40, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16538975529031 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443050113653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_41 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (20665238570439 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215254589453 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨41, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (20665238570439 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215254589453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_42 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16525410883927 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221525863247 / 10000000000000 : ℝ))
      (E := (cell13008 ⟨42, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16525410883927 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221525863247 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_43 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82593178029303 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107631318631 / 50000000000000 : ℝ))
      (E := (cell13008 ⟨43, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82593178029303 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107631318631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_44 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82559325081421 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215266661207 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨44, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82559325081421 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215266661207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_45 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (20631373886699 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215270643771 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨45, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (20631373886699 / 25000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215270643771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_46 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (4124584469819 / 5000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (44305492839 / 2000000000000 : ℝ))
      (E := (cell13008 ⟨46, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (4124584469819 / 5000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (44305492839 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_47 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41228953300637 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215278653673 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨47, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41228953300637 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215278653673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_48 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41212073566361 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215282676661 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨48, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41212073566361 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215282676661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_49 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82390410962111 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (110764335421 / 5000000000000 : ℝ))
      (E := (cell13008 ⟨49, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82390410962111 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (110764335421 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_50 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41178349030487 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215290687231 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨50, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41178349030487 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215290687231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_51 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (16464601680197 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (88611789127 / 4000000000000 : ℝ))
      (E := (cell13008 ⟨51, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (16464601680197 / 20000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (88611789127 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_52 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82289341953957 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215298710081 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨52, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82289341953957 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215298710081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_53 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (10281962336481 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215302747703 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨53, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (10281962336481 / 12500000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215302747703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_54 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (642359988959 / 781250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (110765338923 / 5000000000000 : ℝ))
      (E := (cell13008 ⟨54, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (642359988959 / 781250000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (110765338923 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_55 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41094240805453 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221531073947 / 10000000000000 : ℝ))
      (E := (cell13008 ⟨55, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41094240805453 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (221531073947 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_56 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (41077453868341 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443062960831 / 20000000000000 : ℝ))
      (E := (cell13008 ⟨56, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (41077453868341 / 50000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (443062960831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_57 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82121356936591 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215318790963 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨57, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82121356936591 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215318790963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_58 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (1026097864791 / 1250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215322813847 / 100000000000000 : ℝ))
      (E := (cell13008 ⟨58, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (1026097864791 / 1250000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (2215322813847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13008_59 : CellCertificate 13008 (219570405888743 / 2500000000000000 : ℝ) (403679758293393 / 250000000000000000 : ℝ) (325982193936943 / 10000000000000000 : ℝ)
    (cell13008 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · norm_num [cell13008]
  · have h := gap_lower (n := 13008) (a := (82054324449533 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107663404537 / 50000000000000 : ℝ))
      (E := (cell13008 ⟨59, by decide⟩).energy) (xi := (325982193936943 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13008 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13008]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13008])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13008) (a := (82054324449533 / 100000000000000 : ℝ)) (b := (79151961063 / 50000000000000 : ℝ)) (q := (1107663404537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13008])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13008]

theorem cert13009_40 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41347431738789 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443027302421 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨40, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41347431738789 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443027302421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_41 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82660940120363 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553785132463 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨41, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82660940120363 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553785132463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_42 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41313520132211 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (17305816949 / 781250000000 : ℝ))
      (E := (cell13009 ⟨42, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41313520132211 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (17305816949 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_43 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (10324145485033 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443029714183 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨43, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (10324145485033 / 12500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443029714183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_44 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82559310938551 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443030518311 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨44, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82559310938551 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443030518311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_45 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8252548141009 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107578285431 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨45, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8252548141009 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107578285431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_46 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41245837632917 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443032124949 / 20000000000000 : ℝ))
      (E := (cell13009 ⟨46, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41245837632917 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (443032124949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_47 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (41228946238441 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107582316663 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨47, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (41228946238441 / 50000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107582316663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_48 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82424133014479 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107584297127 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨48, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82424133014479 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107584297127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_49 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82390396850013 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107586311469 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨49, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82390396850013 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107586311469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_50 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (16471336791003 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215176657733 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨50, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (16471336791003 / 20000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215176657733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_51 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (2058074857529 / 2500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553795159171 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨51, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (2058074857529 / 2500000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553795159171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_52 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82289327860261 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215184674713 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨52, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82289327860261 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215184674713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_53 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82255684604277 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107594325193 / 50000000000000 : ℝ))
      (E := (cell13009 ⟨53, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82255684604277 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (1107594325193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_54 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82222064505301 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (22151926783 / 1000000000000 : ℝ))
      (E := (cell13009 ⟨54, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82222064505301 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (22151926783 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_55 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8218846753557 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215196695639 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨55, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8218846753557 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215196695639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_56 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (641835106777 / 781250000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553800174611 / 25000000000000 : ℝ))
      (E := (cell13009 ⟨56, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (641835106777 / 781250000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (553800174611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_57 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (8212134287347 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215204741721 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨57, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (8212134287347 / 10000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215204741721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_58 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (82087815126259 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (138450547623 / 6250000000000 : ℝ))
      (E := (cell13009 ⟨58, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (82087815126259 / 100000000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (138450547623 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13009_59 : CellCertificate 13009 (878254943734911 / 10000000000000000 : ℝ) (1614594870107181 / 1000000000000000000 : ℝ) (325956552985989 / 10000000000000000 : ℝ)
    (cell13009 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · norm_num [cell13009]
  · have h := gap_lower (n := 13009) (a := (5128394399913 / 6250000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215212754603 / 100000000000000 : ℝ))
      (E := (cell13009 ⟨59, by decide⟩).energy) (xi := (325956552985989 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13009 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13009]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13009])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13009) (a := (5128394399913 / 6250000000000 : ℝ)) (b := (158291611829 / 100000000000000 : ℝ)) (q := (2215212754603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13009])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13009]

theorem cert13010_40 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41347424656091 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215022510387 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨40, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41347424656091 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215022510387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_41 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (1653218519223 / 2000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215026524717 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨41, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (1653218519223 / 2000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215026524717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_42 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82627026111387 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107515251071 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨42, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82627026111387 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107515251071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_43 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82593149733403 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215034559081 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨43, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82593149733403 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215034559081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_44 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41279648398929 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553759629393 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨44, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41279648398929 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553759629393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_45 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (2063136681889 / 2500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553760638129 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨45, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (2063136681889 / 2500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553760638129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_46 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41245830568731 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107523272147 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨46, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41245830568731 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107523272147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_47 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (10307234794333 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221505054971 / 10000000000000 : ℝ))
      (E := (cell13010 ⟨47, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (10307234794333 / 12500000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (221505054971 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_48 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82424118898409 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215054566483 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨48, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82424118898409 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215054566483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_49 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41195191370043 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107529296059 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨49, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41195191370043 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107529296059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_50 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82356669851227 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553765655977 / 25000000000000 : ℝ))
      (E := (cell13010 ⟨50, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82356669851227 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (553765655977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_51 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16464596040701 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215066599903 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨51, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16464596040701 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215066599903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_52 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16457862753747 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110753531751 / 5000000000000 : ℝ))
      (E := (cell13010 ⟨52, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16457862753747 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (110753531751 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_53 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41127835259437 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215074666909 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨53, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41127835259437 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215074666909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_54 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41111025213009 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (55376965823 / 2500000000000 : ℝ))
      (E := (cell13010 ⟨54, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41111025213009 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (55376965823 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_55 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (25683891707 / 31250000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215082647487 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨55, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (25683891707 / 31250000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215082647487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_56 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16430975920079 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (443017341343 / 20000000000000 : ℝ))
      (E := (cell13010 ⟨56, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16430975920079 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (443017341343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_57 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (82121328812513 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215090688159 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨57, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (82121328812513 / 100000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215090688159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_58 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (41043900535701 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215094705769 / 100000000000000 : ℝ))
      (E := (cell13010 ⟨58, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (41043900535701 / 50000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (2215094705769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13010_59 : CellCertificate 13010 (878228267843577 / 10000000000000000 : ℝ) (1614470726134243 / 1000000000000000000 : ℝ) (325930916102807 / 10000000000000000 : ℝ)
    (cell13010 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · norm_num [cell13010]
  · have h := gap_lower (n := 13010) (a := (16410859269969 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107549347907 / 50000000000000 : ℝ))
      (E := (cell13010 ⟨59, by decide⟩).energy) (xi := (325930916102807 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13010 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13010]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13010])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13010) (a := (16410859269969 / 20000000000000 : ℝ)) (b := (79139651727 / 50000000000000 : ℝ)) (q := (1107549347907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13010])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13010]

theorem cert13011_40 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41347417574483 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214908504333 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨40, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41347417574483 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214908504333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_41 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82660911804117 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442982503049 / 20000000000000 : ℝ))
      (E := (cell13011 ⟨41, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82660911804117 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442982503049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_42 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82627011960531 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (22149164893 / 1000000000000 : ℝ))
      (E := (cell13011 ⟨42, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82627011960531 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (22149164893 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_43 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82593135588719 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442984108583 / 20000000000000 : ℝ))
      (E := (cell13011 ⟨43, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82593135588719 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (442984108583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_44 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41279641329671 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553731139249 / 25000000000000 : ℝ))
      (E := (cell13011 ⟨44, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41279641329671 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553731139249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_45 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41262726571603 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214928529837 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨45, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41262726571603 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214928529837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_46 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (16498329402253 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214932577347 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨46, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (16498329402253 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214932577347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_47 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82457864234619 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107468289823 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨47, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82457864234619 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107468289823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_48 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82424104784511 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553735148337 / 25000000000000 : ℝ))
      (E := (cell13011 ⟨48, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82424104784511 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (553735148337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_49 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82390368632331 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221494455697 / 10000000000000 : ℝ))
      (E := (cell13011 ⟨49, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82390368632331 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (221494455697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_50 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82356655749609 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107474292879 / 50000000000000 : ℝ))
      (E := (cell13011 ⟨50, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82356655749609 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (1107474292879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_51 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (4116148305401 / 5000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214952617829 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨51, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (4116148305401 / 5000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214952617829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_52 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (41144649839689 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214956591001 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨52, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (41144649839689 / 50000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214956591001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_53 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (2056391410891 / 2500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (88598424801 / 4000000000000 : ℝ))
      (E := (cell13011 ⟨53, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (2056391410891 / 2500000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (88598424801 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_54 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82222036348901 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214964642323 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨54, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82222036348901 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214964642323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_55 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (20547109847849 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (110748432707 / 5000000000000 : ℝ))
      (E := (cell13011 ⟨55, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (20547109847849 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (110748432707 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_56 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82154865535499 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214972651513 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨56, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82154865535499 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214972651513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_57 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (82121314753721 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (44299533789 / 2000000000000 : ℝ))
      (E := (cell13011 ⟨57, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (82121314753721 / 100000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (44299533789 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_58 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (20521946754677 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (34609073507 / 1562500000000 : ℝ))
      (E := (cell13011 ⟨58, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (20521946754677 / 25000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (34609073507 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13011_59 : CellCertificate 13011 (439100797940029 / 5000000000000000 : ℝ) (1614346601250353 / 1000000000000000000 : ℝ) (32590528328637 / 1000000000000000 : ℝ)
    (cell13011 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · norm_num [cell13011]
  · have h := gap_lower (n := 13011) (a := (16410856460649 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214984691927 / 100000000000000 : ℝ))
      (E := (cell13011 ⟨59, by decide⟩).energy) (xi := (32590528328637 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13011 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13011]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13011])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13011) (a := (16410856460649 / 20000000000000 : ℝ)) (b := (158266997003 / 100000000000000 : ℝ)) (q := (2214984691927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13011])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13011]

theorem cert13012_40 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82694820987929 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214794493947 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨40, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82694820987929 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214794493947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_41 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41330448824631 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107399250721 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨41, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41330448824631 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107399250721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_42 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20656749452963 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214802530951 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨42, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20656749452963 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214802530951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_43 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20648280361553 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107403261209 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨43, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20648280361553 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107403261209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_44 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82559268523001 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107405266611 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨44, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82559268523001 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107405266611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_45 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82525439013027 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553703640431 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨45, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82525439013027 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553703640431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_46 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41245816443621 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107409273577 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨46, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41245816443621 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107409273577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_47 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82457850116747 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107411273157 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨47, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82457850116747 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107411273157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_48 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41212045336393 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107413278461 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨48, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41212045336393 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107413278461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_49 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82390354526747 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553707644121 / 25000000000000 : ℝ))
      (E := (cell13012 ⟨49, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82390354526747 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (553707644121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_50 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41178320825081 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214834602293 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨50, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41178320825081 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214834602293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_51 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (5145184500919 / 6250000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214838631433 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨51, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (5145184500919 / 6250000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214838631433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_52 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82289285592189 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214842601717 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨52, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82289285592189 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214842601717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_53 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20563910588643 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107423313951 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨53, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20563910588643 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107423313951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_54 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (1644440445479 / 2000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442970129481 / 20000000000000 : ℝ))
      (E := (cell13012 ⟨54, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (1644440445479 / 2000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (442970129481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_55 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (41094212661279 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214854656473 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨55, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (41094212661279 / 50000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214854656473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_56 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (641834777131 / 781250000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214858651143 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨56, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (641834777131 / 781250000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214858651143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_57 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (20530325174273 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214862686423 / 100000000000000 : ℝ))
      (E := (cell13012 ⟨57, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (20530325174273 / 25000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (2214862686423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_58 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82087772968177 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (221486669881 / 10000000000000 : ℝ))
      (E := (cell13012 ⟨58, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82087772968177 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (221486669881 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13012_59 : CellCertificate 13012 (878174927843447 / 10000000000000000 : ℝ) (1614222495451109 / 1000000000000000000 : ℝ) (6517593090713 / 200000000000000 : ℝ)
    (cell13012 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · norm_num [cell13012]
  · have h := gap_lower (n := 13012) (a := (82054268258807 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107435371473 / 50000000000000 : ℝ))
      (E := (cell13012 ⟨59, by decide⟩).energy) (xi := (6517593090713 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13012 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13012]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13012])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13012) (a := (82054268258807 / 100000000000000 : ℝ)) (b := (158254692473 / 100000000000000 : ℝ)) (q := (1107435371473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13012])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13012]

theorem cert13013_40 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (5168425426817 / 6250000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442936107601 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨40, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (5168425426817 / 6250000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442936107601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_41 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (16532176699317 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214684542109 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨41, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (16532176699317 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214684542109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_42 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82626983665351 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214688568271 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨42, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82626983665351 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214688568271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_43 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82593107305881 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214692556439 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨43, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82593107305881 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214692556439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_44 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20639813597209 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214696563989 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨44, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20639813597209 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214696563989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_45 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41262712442511 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553675147321 / 25000000000000 : ℝ))
      (E := (cell13013 ⟨45, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41262712442511 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553675147321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_46 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82491618765393 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (69209517861 / 3125000000000 : ℝ))
      (E := (cell13013 ⟨46, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82491618765393 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (69209517861 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_47 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (10307229500131 / 12500000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107354313269 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨47, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (10307229500131 / 12500000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107354313269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_48 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (2575752392601 / 3125000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (22147126341 / 1000000000000 : ℝ))
      (E := (cell13013 ⟨48, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (2575752392601 / 3125000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (22147126341 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_49 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41195170211667 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214716650661 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨49, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41195170211667 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214716650661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_50 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (20589156888221 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107360307253 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨50, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (20589156888221 / 25000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107360307253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_51 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82322937923557 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107362320357 / 50000000000000 : ℝ))
      (E := (cell13013 ⟨51, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82322937923557 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (1107362320357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_52 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (2571539734599 / 3125000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214728667171 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨52, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (2571539734599 / 3125000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214728667171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_53 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (10281953534459 / 12500000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214732690539 / 100000000000000 : ℝ))
      (E := (cell13013 ⟨53, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (10281953534459 / 12500000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (2214732690539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_54 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (41111004100583 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276842088409 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨54, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (41111004100583 / 50000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276842088409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_55 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (16437682251177 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442948142723 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨55, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (16437682251177 / 20000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442948142723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_56 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82154837412201 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276843088201 / 12500000000000 : ℝ))
      (E := (cell13013 ⟨56, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82154837412201 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (276843088201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_57 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (82121286642627 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442949747651 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨57, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (82121286642627 / 100000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442949747651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_58 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (641310616561 / 781250000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442950549611 / 20000000000000 : ℝ))
      (E := (cell13013 ⟨58, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (641310616561 / 781250000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (442950549611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13013_59 : CellCertificate 13013 (27442133241651 / 312500000000000 : ℝ) (161409840873211 / 100000000000000000 : ℝ) (162927014924809 / 5000000000000000 : ℝ)
    (cell13013 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · norm_num [cell13013]
  · have h := gap_lower (n := 13013) (a := (8205425421653 / 10000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553689182607 / 25000000000000 : ℝ))
      (E := (cell13013 ⟨59, by decide⟩).energy) (xi := (162927014924809 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13013 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13013]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13013])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13013) (a := (8205425421653 / 10000000000000 : ℝ)) (b := (19780298733 / 12500000000000 : ℝ)) (q := (553689182607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13013])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13013]

theorem cert13014_40 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41347396336197 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221456657773 / 10000000000000 : ℝ))
      (E := (cell13014 ⟨40, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41347396336197 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (221456657773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_41 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41330434673043 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214570578443 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨41, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41330434673043 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214570578443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_42 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82626969521027 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110728730063 / 5000000000000 : ℝ))
      (E := (cell13014 ⟨42, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82626969521027 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (110728730063 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_43 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41296546583863 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214578644977 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨43, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41296546583863 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214578644977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_44 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (16511848051369 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107291324649 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨44, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (16511848051369 / 20000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107291324649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_45 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82525410759191 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553646653129 / 25000000000000 : ℝ))
      (E := (cell13014 ⟨45, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82525410759191 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (553646653129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_46 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (20622901161429 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214590650541 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨46, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (20622901161429 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214590650541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_47 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82457821887521 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107297321747 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨47, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82457821887521 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107297321747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_48 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (1648481249117 / 2000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214598647987 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨48, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (1648481249117 / 2000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214598647987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_49 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82390326322091 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214602661527 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨49, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82390326322091 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214602661527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_50 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (5147288341111 / 6250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107303340703 / 50000000000000 : ℝ))
      (E := (cell13014 ⟨50, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (5147288341111 / 6250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (1107303340703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_51 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41161461917289 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214610704707 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨51, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41161461917289 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214610704707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_52 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41144628712157 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214614728303 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨52, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41144628712157 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214614728303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_53 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41127807099469 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276827343607 / 12500000000000 : ℝ))
      (E := (cell13014 ⟨53, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41127807099469 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (276827343607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_54 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82221994130547 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214622762819 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨54, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82221994130547 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214622762819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_55 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (5136774824461 / 6250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214626766439 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨55, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (5136774824461 / 6250000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214626766439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_56 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (41077411676899 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214630755753 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨56, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (41077411676899 / 50000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214630755753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_57 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (20530318147581 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214634785769 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨57, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (20530318147581 / 25000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214634785769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_58 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82087744873601 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214638792983 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨58, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82087744873601 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214638792983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13014_59 : CellCertificate 13014 (175624320709461 / 2000000000000000 : ℝ) (322794868217791 / 200000000000000000 : ℝ) (325828409227247 / 10000000000000000 : ℝ)
    (cell13014 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · norm_num [cell13014]
  · have h := gap_lower (n := 13014) (a := (82054240176413 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214642832039 / 100000000000000 : ℝ))
      (E := (cell13014 ⟨59, by decide⟩).energy) (xi := (325828409227247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13014 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13014]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13014])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13014) (a := (82054240176413 / 100000000000000 : ℝ)) (b := (158230089177 / 100000000000000 : ℝ)) (q := (2214642832039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13014])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13014]

theorem cert13015_40 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82694778517893 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107226335951 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨40, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82694778517893 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107226335951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_41 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16532171039553 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214456669247 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨41, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16532171039553 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214456669247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_42 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82626955378879 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276807586093 / 12500000000000 : ℝ))
      (E := (cell13015 ⟨42, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82626955378879 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (276807586093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_43 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82593079031747 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214464670339 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨43, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82593079031747 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214464670339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_44 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82559226127029 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55361718257 / 2500000000000 : ℝ))
      (E := (cell13015 ⟨44, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82559226127029 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55361718257 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_45 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82525396635533 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442894538063 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨45, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82525396635533 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442894538063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_46 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20622897632053 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553619181301 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨46, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20622897632053 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553619181301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_47 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41228903888083 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107240357533 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨47, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41228903888083 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107240357533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_48 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41212024175319 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55362119387 / 2500000000000 : ℝ))
      (E := (cell13015 ⟨48, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41212024175319 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (55362119387 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_49 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41195156111509 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442897757209 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨49, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41195156111509 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442897757209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_50 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (20589149841209 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442898560599 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨50, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (20589149841209 / 25000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442898560599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_51 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (10290363718471 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107248382189 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨51, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (10290363718471 / 12500000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107248382189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_52 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82289243343627 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107250392557 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨52, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82289243343627 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107250392557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_53 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (8225560012437 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553626200713 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨53, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (8225560012437 / 10000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553626200713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_54 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82221980062093 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (69203400439 / 3125000000000 : ℝ))
      (E := (cell13015 ⟨54, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82221980062093 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (69203400439 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_55 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82188383129031 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442902562989 / 20000000000000 : ℝ))
      (E := (cell13015 ⟨55, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82188383129031 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (442902562989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_56 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (41077404648779 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107258430367 / 50000000000000 : ℝ))
      (E := (cell13015 ⟨56, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (41077404648779 / 50000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (1107258430367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_57 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82121258540183 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214520888143 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨57, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82121258540183 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214520888143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_58 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (16417546165911 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553631223199 / 25000000000000 : ℝ))
      (E := (cell13015 ⟨58, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (16417546165911 / 20000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (553631223199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13015_59 : CellCertificate 13015 (878094947285957 / 10000000000000000 : ℝ) (1613850292517247 / 1000000000000000000 : ℝ) (32580279266751 / 1000000000000000 : ℝ)
    (cell13015 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · norm_num [cell13015]
  · have h := gap_lower (n := 13015) (a := (82054226138457 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214528870113 / 100000000000000 : ℝ))
      (E := (cell13015 ⟨59, by decide⟩).energy) (xi := (32580279266751 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13015 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13015]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13015])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13015) (a := (82054226138457 / 100000000000000 : ℝ)) (b := (158217790411 / 100000000000000 : ℝ)) (q := (2214528870113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13015])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13015]

theorem cert13016_40 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82694764365571 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (138396172609 / 6250000000000 : ℝ))
      (E := (cell13016 ⟨40, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82694764365571 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (138396172609 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_41 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (4133042052581 / 5000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (88573710229 / 4000000000000 : ℝ))
      (E := (cell13016 ⟨41, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (4133042052581 / 5000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (88573710229 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_42 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41313470619453 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214346771903 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨42, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41313470619453 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214346771903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_43 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41296532448971 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214350809071 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨43, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41296532448971 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214350809071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_44 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82559211999387 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276794350867 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨44, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82559211999387 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276794350867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_45 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (644729550891 / 781250000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442871764537 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨45, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (644729550891 / 781250000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442871764537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_46 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (1031144705161 / 1250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214362854461 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨46, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (1031144705161 / 1250000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214362854461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_47 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82457793666981 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107183420629 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨47, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82457793666981 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107183420629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_48 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20606008561899 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276796354961 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨48, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20606008561899 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276796354961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_49 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41195149063057 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107187423627 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨49, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41195149063057 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107187423627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_50 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (16471317054813 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214378861253 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨50, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (16471317054813 / 20000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214378861253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_51 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20580723915781 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107191439383 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨51, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20580723915781 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107191439383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_52 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (41144614632553 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107193448333 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨52, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (41144614632553 / 50000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107193448333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_53 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82255586051967 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442878182323 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨53, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82255586051967 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442878182323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_54 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20555491498951 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442878984013 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨54, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20555491498951 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442878984013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_55 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (1643767381377 / 2000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276799864783 / 12500000000000 : ℝ))
      (E := (cell13016 ⟨55, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (1643767381377 / 2000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (276799864783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_56 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (2053869881087 / 2500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214402961401 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨56, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (2053869881087 / 2500000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214402961401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_57 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (20530311123051 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214406986203 / 100000000000000 : ℝ))
      (E := (cell13016 ⟨57, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (20530311123051 / 25000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (2214406986203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_58 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (8208771678767 / 10000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442882197659 / 20000000000000 : ℝ))
      (E := (cell13016 ⟨58, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (8208771678767 / 10000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (442882197659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13016_59 : CellCertificate 13016 (878068294947879 / 10000000000000000 : ℝ) (403431565753147 / 250000000000000000 : ℝ) (162888590084691 / 5000000000000000 : ℝ)
    (cell13016 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · norm_num [cell13016]
  · have h := gap_lower (n := 13016) (a := (82054212102661 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107207481549 / 50000000000000 : ℝ))
      (E := (cell13016 ⟨59, by decide⟩).energy) (xi := (162888590084691 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13016 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13016]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13016])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13016) (a := (82054212102661 / 100000000000000 : ℝ)) (b := (39551373391 / 25000000000000 : ℝ)) (q := (1107207481549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13016])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13016]

theorem cert13017_40 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (3307790008617 / 4000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553556226509 / 25000000000000 : ℝ))
      (E := (cell13017 ⟨40, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (3307790008617 / 4000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553556226509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_41 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82660826907651 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (88569155867 / 4000000000000 : ℝ))
      (E := (cell13017 ⟨41, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82660826907651 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (88569155867 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_42 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82626927101109 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214232909557 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨42, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82626927101109 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214232909557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_43 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (10324131345789 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553559235869 / 25000000000000 : ℝ))
      (E := (cell13017 ⟨43, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (10324131345789 / 12500000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553559235869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_44 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41279598936959 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214240938139 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨44, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41279598936959 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214240938139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_45 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (5157835524671 / 6250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (221424495073 / 10000000000000 : ℝ))
      (E := (cell13017 ⟨45, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (5157835524671 / 6250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (221424495073 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_46 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82491562299719 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553562244849 / 25000000000000 : ℝ))
      (E := (cell13017 ⟨46, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82491562299719 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553562244849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_47 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82457779559967 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214252963127 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨47, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82457779559967 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214252963127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_48 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20606005036681 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214256958537 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨48, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20606005036681 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214256958537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_49 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41195142015689 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (55356525553 / 2500000000000 : ℝ))
      (E := (cell13017 ⟨49, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41195142015689 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (55356525553 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_50 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82356571185461 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442853006643 / 20000000000000 : ℝ))
      (E := (cell13017 ⟨50, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82356571185461 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442853006643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_51 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82322881580647 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442853797767 / 20000000000000 : ℝ))
      (E := (cell13017 ⟨51, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82322881580647 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (442853797767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_52 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (82289215188751 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (22142730039 / 1000000000000 : ℝ))
      (E := (cell13017 ⟨52, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (82289215188751 / 100000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (22142730039 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_53 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (8225557198173 / 10000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107138508029 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨53, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (8225557198173 / 10000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107138508029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_54 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41110975965839 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276785135109 / 12500000000000 : ℝ))
      (E := (cell13017 ⟨54, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41110975965839 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (276785135109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_55 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (5136772188177 / 6250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553571269099 / 25000000000000 : ℝ))
      (E := (cell13017 ⟨55, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (5136772188177 / 6250000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (553571269099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_56 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (20538695297891 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107144528877 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨56, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (20538695297891 / 25000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107144528877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_57 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (41060615223193 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44285861599 / 2000000000000 : ℝ))
      (E := (cell13017 ⟨57, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (41060615223193 / 50000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (44285861599 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_58 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (16417540549589 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107148539741 / 50000000000000 : ℝ))
      (E := (cell13017 ⟨58, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (16417540549589 / 20000000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (1107148539741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13017_59 : CellCertificate 13017 (878041646532163 / 10000000000000000 : ℝ) (1613602252570583 / 1000000000000000000 : ℝ) (65150314346367 / 2000000000000000 : ℝ)
    (cell13017 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · norm_num [cell13017]
  · have h := gap_lower (n := 13017) (a := (2564193689657 / 3125000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214301110993 / 100000000000000 : ℝ))
      (E := (cell13017 ⟨59, by decide⟩).energy) (xi := (65150314346367 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13017 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13017]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13017])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13017) (a := (2564193689657 / 3125000000000 : ℝ)) (b := (158193198637 / 100000000000000 : ℝ)) (q := (2214301110993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13017])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13017]

theorem cert13018_40 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (646052625527 / 781250000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107055523 / 50000000000 : ℝ))
      (E := (cell13018 ⟨40, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (646052625527 / 781250000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107055523 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_41 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41330406382929 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107057516649 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨41, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41330406382929 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107057516649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_42 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82626912965487 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442823808577 / 20000000000000 : ℝ))
      (E := (cell13018 ⟨42, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82626912965487 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442823808577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_43 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16518607327371 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553530768389 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨43, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16518607327371 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553530768389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_44 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82559183750623 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276765883127 / 12500000000000 : ℝ))
      (E := (cell13018 ⟨44, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82559183750623 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (276765883127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_45 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20631338569399 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214131074451 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨45, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20631338569399 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214131074451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_46 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (8249154818873 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214135100007 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨46, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (8249154818873 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214135100007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_47 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82457765455123 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (69191848113 / 3125000000000 : ℝ))
      (E := (cell13018 ⟨47, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82457765455123 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (69191848113 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_48 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82424006048021 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214143132031 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨48, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82424006048021 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214143132031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_49 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82390269938811 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553536783419 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨49, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82390269938811 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553536783419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_50 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (3294262283961 / 4000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442830228369 / 20000000000000 : ℝ))
      (E := (cell13018 ⟨50, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (3294262283961 / 4000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (442830228369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_51 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82322867500337 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (110707757681 / 5000000000000 : ℝ))
      (E := (cell13018 ⟨51, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82322867500337 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (110707757681 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_52 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (41144600557281 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107079582937 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨52, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (41144600557281 / 50000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107079582937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_53 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (10281944739207 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553540793817 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨53, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (10281944739207 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553540793817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_54 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (20555484467429 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214167178257 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨54, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (20555484467429 / 25000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214167178257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_55 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (2568385654843 / 3125000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107085615107 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨55, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (2568385654843 / 3125000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107085615107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_56 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (8215476714181 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (138385950559 / 6250000000000 : ℝ))
      (E := (cell13018 ⟨56, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (8215476714181 / 10000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (138385950559 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_57 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (10265152050341 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214179228559 / 100000000000000 : ℝ))
      (E := (cell13018 ⟨57, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (10265152050341 / 12500000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (2214179228559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_58 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (82087688710379 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553545806389 / 25000000000000 : ℝ))
      (E := (cell13018 ⟨58, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (82087688710379 / 100000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (553545806389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13018_59 : CellCertificate 13018 (8780150020379 / 100000000000000 : ℝ) (1613478261186837 / 1000000000000000000 : ℝ) (81431491838461 / 2500000000000000 : ℝ)
    (cell13018 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · norm_num [cell13018]
  · have h := gap_lower (n := 13018) (a := (16410836807509 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107093627289 / 50000000000000 : ℝ))
      (E := (cell13018 ⟨59, by decide⟩).energy) (xi := (81431491838461 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13018 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13018]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13018])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13018) (a := (16410836807509 / 20000000000000 : ℝ)) (b := (15818090563 / 10000000000000 : ℝ)) (q := (1107093627289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13018])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13018]

theorem cert13019_40 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (646052515013 / 781250000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106998620207 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨40, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (646052515013 / 781250000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1106998620207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_41 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (258314995707 / 312500000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214001224397 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨41, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (258314995707 / 312500000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214001224397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_42 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82626898832039 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107002615357 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨42, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82626898832039 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107002615357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_43 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (20648255627393 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214009258161 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨43, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (20648255627393 / 25000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214009258161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_44 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82559169629499 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214013246443 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨44, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82559169629499 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214013246443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_45 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82525340162627 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107008626373 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨45, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82525340162627 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107008626373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_46 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82491534079911 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442804255043 / 20000000000000 : ℝ))
      (E := (cell13019 ⟨46, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82491534079911 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442804255043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_47 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82457751352449 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442805062357 / 20000000000000 : ℝ))
      (E := (cell13019 ⟨47, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82457751352449 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (442805062357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_48 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41211995975743 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214029301207 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨48, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41211995975743 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214029301207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_49 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82390255848411 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (34594270311 / 1562500000000 : ℝ))
      (E := (cell13019 ⟨49, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82390255848411 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (34594270311 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_50 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (16471308602951 / 20000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214037305171 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨50, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (16471308602951 / 20000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214037305171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_51 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (5145178338887 / 6250000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (221404131409 / 10000000000000 : ℝ))
      (E := (cell13019 ⟨51, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (5145178338887 / 6250000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (221404131409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_52 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82289187042537 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107022661767 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨52, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82289187042537 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107022661767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_53 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82255543847747 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107024694623 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨53, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82255543847747 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107024694623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_54 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82221923809917 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (110702669477 / 5000000000000 : ℝ))
      (E := (cell13019 ⟨54, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82221923809917 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (110702669477 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_55 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (41094163450641 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (55351434493 / 2500000000000 : ℝ))
      (E := (cell13019 ⟨55, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (41094163450641 / 50000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (55351434493 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_56 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82154753094217 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (88562456599 / 4000000000000 : ℝ))
      (E := (cell13019 ⟨56, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82154753094217 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (88562456599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_57 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82121202361231 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107032716017 / 50000000000000 : ℝ))
      (E := (cell13019 ⟨57, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82121202361231 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (1107032716017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_58 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (82087674674973 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214069426519 / 100000000000000 : ℝ))
      (E := (cell13019 ⟨58, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (82087674674973 / 100000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (2214069426519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13019_59 : CellCertificate 13019 (109748545183023 / 1250000000000000 : ℝ) (1613354288856957 / 1000000000000000000 : ℝ) (65140073406877 / 2000000000000000 : ℝ)
    (cell13019 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · norm_num [cell13019]
  · have h := gap_lower (n := 13019) (a := (3282166800329 / 4000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553518363269 / 25000000000000 : ℝ))
      (E := (cell13019 ⟨59, by decide⟩).energy) (xi := (65140073406877 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13019 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13019]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13019])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13019) (a := (3282166800329 / 4000000000000 : ℝ)) (b := (158168614541 / 100000000000000 : ℝ)) (q := (553518363269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13019])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13019]

theorem cert13020_40 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82694707778047 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276735428813 / 12500000000000 : ℝ))
      (E := (cell13020 ⟨40, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82694707778047 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276735428813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_41 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82660784488797 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213887411171 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨41, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82660784488797 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213887411171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_42 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (16525376940153 / 20000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213891414219 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨42, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (16525376940153 / 20000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213891414219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_43 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41296504192231 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213895438443 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨43, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41296504192231 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213895438443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_44 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82559155510547 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553474855887 / 25000000000000 : ℝ))
      (E := (cell13020 ⟨44, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82559155510547 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553474855887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_45 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82525326049829 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442780697123 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨45, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82525326049829 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442780697123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_46 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41245759986631 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442781489221 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨46, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41245759986631 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442781489221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_47 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (10307217156493 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442782295927 / 20000000000000 : ℝ))
      (E := (cell13020 ⟨47, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (10307217156493 / 12500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (442782295927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_48 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (515149861607 / 625000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553478881257 / 25000000000000 : ℝ))
      (E := (cell13020 ⟨48, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (515149861607 / 625000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (553478881257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_49 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82390241760179 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106959760401 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨49, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82390241760179 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106959760401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_50 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82356528932651 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276740440399 / 12500000000000 : ℝ))
      (E := (cell13020 ⟨50, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82356528932651 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (276740440399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_51 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (20580709836553 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (6918523529 / 312500000000 : ℝ))
      (E := (cell13020 ⟨51, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (20580709836553 / 25000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (6918523529 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_52 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82289172972677 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213931535937 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨52, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82289172972677 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213931535937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_53 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (10281941223 / 12500000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213935539829 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨53, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (10281941223 / 12500000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213935539829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_54 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (2055547743807 / 2500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213939596511 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨54, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (2055547743807 / 2500000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213939596511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_55 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (328753251399 / 400000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106971792021 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨55, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (328753251399 / 400000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106971792021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_56 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (5134671190549 / 6250000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213947616697 / 100000000000000 : ℝ))
      (E := (cell13020 ⟨56, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (5134671190549 / 6250000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (2213947616697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_57 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (41060594160947 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106975815599 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨57, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (41060594160947 / 50000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106975815599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_58 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (3283506425669 / 4000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106977811587 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨58, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (3283506425669 / 4000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106977811587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13020_59 : CellCertificate 13020 (877961724810107 / 10000000000000000 : ℝ) (1613230335576551 / 1000000000000000000 : ℝ) (325674770772431 / 10000000000000000 : ℝ)
    (cell13020 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · norm_num [cell13020]
  · have h := gap_lower (n := 13020) (a := (82054155981063 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106979823633 / 50000000000000 : ℝ))
      (E := (cell13020 ⟨59, by decide⟩).energy) (xi := (325674770772431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13020 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13020]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13020])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13020) (a := (82054155981063 / 100000000000000 : ℝ)) (b := (15815632537 / 10000000000000 : ℝ)) (q := (1106979823633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13020])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13020]

theorem cert13021_40 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (16538938727321 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (221376961627 / 10000000000000 : ℝ))
      (E := (cell13021 ⟨40, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (16538938727321 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (221376961627 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_41 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10332596294191 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276721706553 / 12500000000000 : ℝ))
      (E := (cell13021 ⟨41, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10332596294191 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276721706553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_42 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (5164179410729 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213777652227 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨42, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (5164179410729 / 6250000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213777652227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_43 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20648248565381 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213781673251 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨43, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20648248565381 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213781673251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_44 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82559141393767 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553446413801 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨44, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82559141393767 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553446413801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_45 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41262655969601 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213789655269 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨45, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41262655969601 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213789655269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_46 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41245752934391 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213793671593 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨46, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41245752934391 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213793671593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_47 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82457723153607 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553449425527 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨47, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82457723153607 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553449425527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_48 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82423963764921 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (34590651337 / 1562500000000 : ℝ))
      (E := (cell13021 ⟨48, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82423963764921 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (34590651337 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_49 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82390227674113 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276725717173 / 12500000000000 : ℝ))
      (E := (cell13021 ⟨49, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82390227674113 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (276725717173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_50 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82356514852713 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106904868449 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨50, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82356514852713 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106904868449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_51 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82322825272397 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442762748031 / 20000000000000 : ℝ))
      (E := (cell13021 ⟨51, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82322825272397 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (442762748031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_52 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (4114457945249 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553454436007 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨52, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (4114457945249 / 5000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553454436007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_53 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82255515722417 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106910902131 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨53, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82255515722417 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106910902131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_54 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (16444379139361 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213825799169 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨54, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (16444379139361 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213825799169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_55 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (82188298800379 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106914892027 / 50000000000000 : ℝ))
      (E := (cell13021 ⟨55, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (82188298800379 / 100000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (1106914892027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_56 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (10269340625689 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213833814107 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨56, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (10269340625689 / 12500000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213833814107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_57 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (16424234856943 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213837826053 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨57, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (16424234856943 / 20000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213837826053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_58 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (20521911652659 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213841815519 / 100000000000000 : ℝ))
      (E := (cell13021 ⟨58, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (20521911652659 / 25000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (2213841815519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13021_59 : CellCertificate 13021 (877935092074761 / 10000000000000000 : ℝ) (1613106401341229 / 1000000000000000000 : ℝ) (325649178566959 / 10000000000000000 : ℝ)
    (cell13021 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · norm_num [cell13021]
  · have h := gap_lower (n := 13021) (a := (41027070978029 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553461459287 / 25000000000000 : ℝ))
      (E := (cell13021 ⟨59, by decide⟩).energy) (xi := (325649178566959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13021 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13021]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13021])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13021) (a := (41027070978029 / 50000000000000 : ℝ)) (b := (158144038117 / 100000000000000 : ℝ)) (q := (553461459287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13021])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13021]

theorem cert13022_40 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41347339748669 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (221365585649 / 10000000000000 : ℝ))
      (E := (cell13022 ⟨40, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41347339748669 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (221365585649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_41 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82660756220433 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213659889353 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨41, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82660756220433 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213659889353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_42 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (1291044631949 / 1562500000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (276707985739 / 12500000000000 : ℝ))
      (E := (cell13022 ⟨42, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (1291044631949 / 1562500000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (276707985739 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_43 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82592980140757 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213667903739 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨43, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82592980140757 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213667903739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_44 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41279563639579 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106835941269 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨44, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41279563639579 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106835941269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_45 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (16505059566149 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (276709492299 / 12500000000000 : ℝ))
      (E := (cell13022 ⟨45, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (16505059566149 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (276709492299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_46 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (10311436470809 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (6917749849 / 312500000000 : ℝ))
      (E := (cell13022 ⟨46, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (10311436470809 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (6917749849 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_47 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (41228854528719 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442736784053 / 20000000000000 : ℝ))
      (E := (cell13022 ⟨47, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (41228854528719 / 50000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (442736784053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_48 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82423949674889 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106843979861 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨48, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82423949674889 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106843979861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_49 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82390213590213 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213691949651 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨49, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82390213590213 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213691949651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_50 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82356500774941 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (22136960053 / 1000000000000 : ℝ))
      (E := (cell13022 ⟨50, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82356500774941 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (22136960053 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_51 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82322811200747 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213700005751 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨51, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82322811200747 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213700005751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_52 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82289144839447 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213704006863 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨52, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82289144839447 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213704006863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_53 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (20563875415749 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213708005301 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨53, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (20563875415749 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213708005301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_54 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (20555470410873 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106856028311 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨54, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (20555470410873 / 25000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106856028311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_55 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (5136767797073 / 6250000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553429009721 / 25000000000000 : ℝ))
      (E := (cell13022 ⟨55, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (5136767797073 / 6250000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (553429009721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_56 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (82154710964399 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (55343001659 / 2500000000000 : ℝ))
      (E := (cell13022 ⟨56, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (82154710964399 / 100000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (55343001659 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_57 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (16424232049939 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (8647359671 / 390625000000 : ℝ))
      (E := (cell13022 ⟨57, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (16424232049939 / 20000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (8647359671 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_58 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (10260954072713 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213728062757 / 100000000000000 : ℝ))
      (E := (cell13022 ⟨58, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (10260954072713 / 12500000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (2213728062757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13022_59 : CellCertificate 13022 (877908463257239 / 10000000000000000 : ℝ) (1612982486146603 / 1000000000000000000 : ℝ) (65124718083389 / 2000000000000000 : ℝ)
    (cell13022 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · norm_num [cell13022]
  · have h := gap_lower (n := 13022) (a := (8205412793321 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106866040973 / 50000000000000 : ℝ))
      (E := (cell13022 ⟨59, by decide⟩).energy) (xi := (65124718083389 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13022 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13022]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13022])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13022) (a := (8205412793321 / 10000000000000 : ℝ)) (b := (79065876391 / 50000000000000 : ℝ)) (q := (1106866040973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13022])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13022]

theorem cert13023_40 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16538933072049 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106771075583 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨40, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16538933072049 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106771075583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_41 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82660742089511 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106773060981 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨41, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82660742089511 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106773060981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_42 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (4131342115999 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106775087051 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨42, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (4131342115999 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106775087051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_43 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41296483011081 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553388547189 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨43, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41296483011081 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553388547189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_44 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82559113166719 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553389541107 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨44, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82559113166719 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553389541107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_45 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82525283724457 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442712431661 / 20000000000000 : ℝ))
      (E := (cell13023 ⟨45, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82525283724457 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442712431661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_46 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82491477666329 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442713233707 / 20000000000000 : ℝ))
      (E := (cell13023 ⟨46, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82491477666329 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (442713233707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_47 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82457694963437 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213570193047 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨47, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82457694963437 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213570193047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_48 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (5151495974189 / 6250000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213574229561 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨48, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (5151495974189 / 6250000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213574229561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_49 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82390199508479 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213578216593 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨49, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82390199508479 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213578216593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_50 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82356486699333 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213582269391 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨50, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82356486699333 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213582269391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_51 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (4116139856563 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553396566759 / 25000000000000 : ℝ))
      (E := (cell13023 ⟨51, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (4116139856563 / 5000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (553396566759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_52 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (20572282694019 / 25000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213590265389 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨52, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (20572282694019 / 25000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213590265389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_53 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82255487605737 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213594261113 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨53, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82255487605737 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213594261113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_54 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82221867592339 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106799154883 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨54, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82221867592339 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106799154883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_55 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41094135354059 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106801144703 / 50000000000000 : ℝ))
      (E := (cell13023 ⟨55, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41094135354059 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (1106801144703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_56 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (16430939385089 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213606314307 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨56, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (16430939385089 / 20000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213606314307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_57 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (82121146216833 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276701290149 / 12500000000000 : ℝ))
      (E := (cell13023 ⟨57, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (82121146216833 / 100000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276701290149 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_58 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (8208761855493 / 10000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276701795611 / 12500000000000 : ℝ))
      (E := (cell13023 ⟨58, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (8208761855493 / 10000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (276701795611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13023_59 : CellCertificate 13023 (175576367671327 / 2000000000000000 : ℝ) (403214647497071 / 250000000000000000 : ℝ) (162799003160683 / 5000000000000000 : ℝ)
    (cell13023 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · norm_num [cell13023]
  · have h := gap_lower (n := 13023) (a := (41027056956259 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213618381663 / 100000000000000 : ℝ))
      (E := (cell13023 ⟨59, by decide⟩).energy) (xi := (162799003160683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13023 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13023]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13023])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13023) (a := (41027056956259 / 50000000000000 : ℝ)) (b := (158119469363 / 100000000000000 : ℝ)) (q := (2213618381663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13023])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13023]

theorem cert13024_40 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41347325612663 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (27667855519 / 1250000000000 : ℝ))
      (E := (cell13024 ⟨40, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41347325612663 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (27667855519 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_41 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41330363980381 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213432409051 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨41, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41330363980381 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213432409051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_42 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (20656707049349 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213436457973 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨42, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (20656707049349 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213436457973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_43 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41296475952869 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213440469453 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨43, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41296475952869 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213440469453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_44 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (1651181981129 / 2000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106722220999 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨44, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (1651181981129 / 2000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106722220999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_45 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82525269620337 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213448491691 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨45, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82525269620337 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213448491691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_46 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (16498292713671 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213452498909 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨46, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (16498292713671 / 20000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213452498909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_47 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82457680871603 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276682065057 / 12500000000000 : ℝ))
      (E := (cell13024 ⟨47, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82457680871603 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276682065057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_48 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (3296956860053 / 4000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106730247543 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨48, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (3296956860053 / 4000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106730247543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_49 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (8239018542891 / 10000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221346453821 / 10000000000000 : ℝ))
      (E := (cell13024 ⟨49, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (8239018542891 / 10000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (221346453821 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_50 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82356472625889 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (138341783073 / 6250000000000 : ℝ))
      (E := (cell13024 ⟨50, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82356472625889 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (138341783073 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_51 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82322783063937 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276684065501 / 12500000000000 : ℝ))
      (E := (cell13024 ⟨51, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82322783063937 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (276684065501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_52 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (20572279178717 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213476578663 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨52, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (20572279178717 / 25000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213476578663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_53 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (1028193419383 / 1250000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (138342535731 / 6250000000000 : ℝ))
      (E := (cell13024 ⟨53, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (1028193419383 / 1250000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (138342535731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_54 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82221853543347 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213484558601 / 100000000000000 : ℝ))
      (E := (cell13024 ⟨54, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82221853543347 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (2213484558601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_55 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (41094128332613 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (8853954379 / 400000000000 : ℝ))
      (E := (cell13024 ⟨55, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (41094128332613 / 50000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (8853954379 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_56 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (1643093657773 / 2000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106746308549 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨56, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (1643093657773 / 2000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106746308549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_57 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82121132186129 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106748310739 / 50000000000000 : ℝ))
      (E := (cell13024 ⟨57, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82121132186129 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (1106748310739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_58 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (10260950566289 / 12500000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442700120703 / 20000000000000 : ℝ))
      (E := (cell13024 ⟨58, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (10260950566289 / 12500000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (442700120703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

theorem cert13024_59 : CellCertificate 13024 (877855217372043 / 10000000000000000 : ℝ) (322546942572377 / 200000000000000000 : ℝ) (325572426279197 / 10000000000000000 : ℝ)
    (cell13024 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · norm_num [cell13024]
  · have h := gap_lower (n := 13024) (a := (82054099893981 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553376154463 / 25000000000000 : ℝ))
      (E := (cell13024 ⟨59, by decide⟩).energy) (xi := (325572426279197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13024 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13024]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13024])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13024) (a := (82054099893981 / 100000000000000 : ℝ)) (b := (158107187861 / 100000000000000 : ℝ)) (q := (553376154463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13024])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13024]

end BstLean.Part268
