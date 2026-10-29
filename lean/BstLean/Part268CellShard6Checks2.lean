import BstLean.Part268CellShard6Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12500_40 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (4134832362209 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138473751571 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨40, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (4134832362209 / 5000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138473751571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_41 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41331290829237 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284618936731 / 12500000000000 : ℝ))
      (E := (cell12500 ⟨41, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41331290829237 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (284618936731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_42 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82628539770107 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276955471247 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨42, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82628539770107 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276955471247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_43 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82594521549231 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569239873407 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨43, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82594521549231 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569239873407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_44 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41280263483077 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455392700301 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨44, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41280263483077 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455392700301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_45 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82526555991329 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227696749393 / 10000000000000 : ℝ))
      (E := (cell12500 ⟨45, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82526555991329 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (227696749393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_46 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82492608595361 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455394293947 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨46, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82492608595361 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455394293947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_47 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82458684749003 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276975486427 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨47, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82458684749003 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276975486427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_48 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41212392211577 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276979483563 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨48, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41212392211577 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276979483563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_49 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82390907588859 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276983518267 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨49, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82390907588859 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276983518267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_50 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82357054217309 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455397494131 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨50, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82357054217309 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455397494131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_51 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41161612139921 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276991515373 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨51, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41161612139921 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2276991515373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_52 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (16457883549587 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138497736539 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨52, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (16457883549587 / 20000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138497736539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_53 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (20563908648303 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138499759067 / 50000000000000 : ℝ))
      (E := (cell12500 ⟨53, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (20563908648303 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (1138499759067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_54 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82221874787437 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2277003529691 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨54, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82221874787437 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2277003529691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_55 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (20547034575629 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (113850375233 / 5000000000000 : ℝ))
      (E := (cell12500 ⟨55, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (20547034575629 / 25000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (113850375233 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_56 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (2567325784703 / 3125000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71156609339 / 3125000000000 : ℝ))
      (E := (cell12500 ⟨56, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (2567325784703 / 3125000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (71156609339 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_57 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82120735183563 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2277015508821 / 100000000000000 : ℝ))
      (E := (cell12500 ⟨57, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82120735183563 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (2277015508821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_58 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (41043534247021 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455403906187 / 20000000000000 : ℝ))
      (E := (cell12500 ⟨58, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (41043534247021 / 50000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (455403906187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12500_59 : CellCertificate 12500 (2788636686689 / 31250000000000 : ℝ) (1680363136043441 / 1000000000000000000 : ℝ) (339557587310217 / 10000000000000000 : ℝ)
    (cell12500 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · norm_num [cell12500]
  · have h := gap_lower (n := 12500) (a := (82053425014397 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569255875541 / 25000000000000 : ℝ))
      (E := (cell12500 ⟨59, by decide⟩).energy) (xi := (339557587310217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12500 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12500]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12500])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12500) (a := (82053425014397 / 100000000000000 : ℝ)) (b := (164816889259 / 100000000000000 : ℝ)) (q := (569255875541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12500])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12500]

theorem cert12501_40 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41348322197221 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276816590667 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨40, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41348322197221 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276816590667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_41 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82662579118881 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276820564857 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨41, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82662579118881 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276820564857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_42 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82628537540229 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276824585221 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨42, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82628537540229 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276824585221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_43 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82594519628641 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276828592519 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨43, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82594519628641 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276828592519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_44 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (10320065669303 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276832586017 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨44, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (10320065669303 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276832586017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_45 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82526554688033 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569209141191 / 25000000000000 : ℝ))
      (E := (cell12501 ⟨45, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82526554688033 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (569209141191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_46 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41246303800037 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138420293231 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨46, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41246303800037 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138420293231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_47 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (824586840613 / 1000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276844590903 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨47, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (824586840613 / 1000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276844590903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_48 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (8242478404261 / 10000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284606072061 / 12500000000000 : ℝ))
      (E := (cell12501 ⟨48, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (8242478404261 / 10000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284606072061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_49 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82390907515051 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276852600341 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨49, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82390907515051 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276852600341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_50 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (10294631806227 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276856601539 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨50, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (10294631806227 / 12500000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276856601539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_51 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (257260077557 / 312500000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (28460757223 / 1250000000000 : ℝ))
      (E := (cell12501 ⟨51, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (257260077557 / 312500000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (28460757223 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_52 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20572354647951 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138432292899 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨52, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20572354647951 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138432292899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_53 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (20563908935533 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276868563783 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨53, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (20563908935533 / 25000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276868563783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_54 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82221876240987 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (91074902719 / 4000000000000 : ℝ))
      (E := (cell12501 ⟨54, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82221876240987 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (91074902719 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_55 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82188140060279 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455375319071 / 20000000000000 : ℝ))
      (E := (cell12501 ⟨55, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82188140060279 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (455375319071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_56 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (82154427172053 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284610072949 / 12500000000000 : ℝ))
      (E := (cell12501 ⟨56, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (82154427172053 / 100000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (284610072949 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_57 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (5132546096781 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276884588309 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨57, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (5132546096781 / 6250000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276884588309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_58 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (41043535580967 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276888605859 / 100000000000000 : ℝ))
      (E := (cell12501 ⟨58, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (41043535580967 / 50000000000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (2276888605859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12501_59 : CellCertificate 12501 (446167469926593 / 5000000000000000 : ℝ) (840114336423563 / 500000000000000000 : ℝ) (42441217093877 / 1250000000000000 : ℝ)
    (cell12501 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · norm_num [cell12501]
  · have h := gap_lower (n := 12501) (a := (1282084812263 / 1562500000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138446286609 / 50000000000000 : ℝ))
      (E := (cell12501 ⟨59, by decide⟩).energy) (xi := (42441217093877 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12501 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12501]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12501])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12501) (a := (1282084812263 / 1562500000000 : ℝ)) (b := (164803537959 / 100000000000000 : ℝ)) (q := (1138446286609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12501])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12501]

theorem cert12502_40 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (8269664154563 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276685733557 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨40, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (8269664154563 / 10000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276685733557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_41 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (3306503063207 / 4000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455337938259 / 20000000000000 : ℝ))
      (E := (cell12502 ⟨41, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (3306503063207 / 4000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455337938259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_42 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (103285669139 / 125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284586711989 / 12500000000000 : ℝ))
      (E := (cell12502 ⟨42, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (103285669139 / 125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (284586711989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_43 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41297258854431 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455339537633 / 20000000000000 : ℝ))
      (E := (cell12502 ⟨43, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41297258854431 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (455339537633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_44 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82560523743467 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (35573464471 / 1562500000000 : ℝ))
      (E := (cell12502 ⟨44, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82560523743467 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (35573464471 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_45 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82526553385473 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569176422819 / 25000000000000 : ℝ))
      (E := (cell12502 ⟨45, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82526553385473 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (569176422819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_46 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (16498521321097 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113835485003 / 5000000000000 : ℝ))
      (E := (cell12502 ⟨46, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (16498521321097 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113835485003 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_47 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (5153667710891 / 6250000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (227671369229 / 10000000000000 : ℝ))
      (E := (cell12502 ⟨47, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (5153667710891 / 6250000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (227671369229 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_48 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (2575774489459 / 3125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276717725279 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨48, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (2575774489459 / 3125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276717725279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_49 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20597726860457 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138360869171 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨49, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20597726860457 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138360869171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_50 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82357054682869 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276725729449 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨50, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82357054682869 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276725729449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_51 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (20580806339287 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276729696357 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨51, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (20580806339287 / 25000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276729696357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_52 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (16457883887229 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113836684781 / 5000000000000 : ℝ))
      (E := (cell12502 ⟨52, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (16457883887229 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (113836684781 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_53 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (16451127378297 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276737724641 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨53, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (16451127378297 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276737724641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_54 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (16444375538987 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276741721553 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨54, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (16444375538987 / 20000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276741721553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_55 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (102735177273 / 125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276745742351 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨55, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (102735177273 / 125000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276745742351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_56 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82154429233931 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138374862349 / 50000000000000 : ℝ))
      (E := (cell12502 ⟨56, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82154429233931 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (1138374862349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_57 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82120739913713 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276753724219 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨57, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82120739913713 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276753724219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_58 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (41043536915037 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276757737267 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨58, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (41043536915037 / 50000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276757737267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12502_59 : CellCertificate 12502 (178461228879307 / 2000000000000000 : ℝ) (1680094231168663 / 1000000000000000000 : ℝ) (339501890844129 / 10000000000000000 : ℝ)
    (cell12502 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · norm_num [cell12502]
  · have h := gap_lower (n := 12502) (a := (82053430955477 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276761759993 / 100000000000000 : ℝ))
      (E := (cell12502 ⟨59, by decide⟩).energy) (xi := (339501890844129 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12502 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12502]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12502])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12502) (a := (82053430955477 / 100000000000000 : ℝ)) (b := (82395094421 / 50000000000000 : ℝ)) (q := (2276761759993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12502])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12502]

theorem cert12503_40 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16539327739549 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138277436541 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨40, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16539327739549 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138277436541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_41 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82662574042357 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276558873159 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨41, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82662574042357 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276558873159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_42 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41314266541511 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455312584173 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨42, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41314266541511 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455312584173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_43 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16518903157979 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276566898161 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨43, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16518903157979 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276566898161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_44 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (16512104426657 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455314184377 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨44, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (16512104426657 / 20000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455314184377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_45 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (1289477376307 / 1562500000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455314974693 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨45, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (1289477376307 / 1562500000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455314974693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_46 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82492605611593 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138289434699 / 50000000000000 : ℝ))
      (E := (cell12503 ⟨46, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82492605611593 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (1138289434699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_47 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (644208458499 / 781250000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227658290837 / 10000000000000 : ℝ))
      (E := (cell12503 ⟨47, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (644208458499 / 781250000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (227658290837 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_48 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82424783283389 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569146732483 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨48, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82424783283389 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569146732483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_49 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (8239090736919 / 10000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569147733067 / 25000000000000 : ℝ))
      (E := (cell12503 ⟨49, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (8239090736919 / 10000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (569147733067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_50 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82357054916469 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276594913347 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨50, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82357054916469 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276594913347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_51 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (20580806474141 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284574866239 / 12500000000000 : ℝ))
      (E := (cell12503 ⟨51, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (20580806474141 / 25000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284574866239 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_52 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82289420280957 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455320584113 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨52, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82289420280957 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455320584113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_53 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82255638041273 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276606882639 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨53, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82255638041273 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276606882639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_54 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41110939574639 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276610931369 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨54, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41110939574639 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276610931369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_55 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82188143576881 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276614886563 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨55, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82188143576881 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276614886563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_56 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (8215443129613 / 10000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455323784433 / 20000000000000 : ℝ))
      (E := (cell12503 ⟨56, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (8215443129613 / 10000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (455323784433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_57 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (41060371139607 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284577864569 / 12500000000000 : ℝ))
      (E := (cell12503 ⟨57, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (41060371139607 / 50000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (284577864569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_58 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (4104353824923 / 5000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (56915673129 / 2500000000000 : ℝ))
      (E := (cell12503 ⟨58, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (4104353824923 / 5000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (56915673129 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12503_59 : CellCertificate 12503 (892277353369453 / 10000000000000000 : ℝ) (1679959811002887 / 1000000000000000000 : ℝ) (42434256198533 / 1250000000000000 : ℝ)
    (cell12503 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · norm_num [cell12503]
  · have h := gap_lower (n := 12503) (a := (82053433926333 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276630944137 / 100000000000000 : ℝ))
      (E := (cell12503 ⟨59, by decide⟩).energy) (xi := (42434256198533 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12503 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12503]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12503])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12503) (a := (82053433926333 / 100000000000000 : ℝ)) (b := (164776841909 / 100000000000000 : ℝ)) (q := (2276630944137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12503])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12503]

theorem cert12504_40 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (2584269870337 / 3125000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455284825341 / 20000000000000 : ℝ))
      (E := (cell12504 ⟨40, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (2584269870337 / 3125000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455284825341 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_41 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41331285752713 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138214055227 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨41, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41331285752713 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138214055227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_42 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (20657132713923 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138216071269 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨42, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (20657132713923 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138216071269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_43 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82594513871739 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138218052457 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨43, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82594513871739 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138218052457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_44 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (660484164191 / 800000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276440114423 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨44, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (660484164191 / 800000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276440114423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_45 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82526550782559 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138222055667 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨45, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82526550782559 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138222055667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_46 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41246302309199 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276448153349 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨46, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41246302309199 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276448153349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_47 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (20614670500537 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276452121363 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨47, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (20614670500537 / 25000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276452121363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_48 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82424782904711 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276456131537 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨48, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82424782904711 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276456131537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_49 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (16478181459427 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455292024637 / 20000000000000 : ℝ))
      (E := (cell12504 ⟨49, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (16478181459427 / 20000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (455292024637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_50 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41178527575307 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138232076619 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨50, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41178527575307 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138232076619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_51 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82323226436489 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138234080267 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨51, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82323226436489 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138234080267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_52 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (514308882039 / 625000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284559017827 / 12500000000000 : ℝ))
      (E := (cell12504 ⟨52, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (514308882039 / 625000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (284559017827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_53 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (41127819595747 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276476155849 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨53, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (41127819595747 / 50000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276476155849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_54 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82221880604017 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276480138367 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨54, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82221880604017 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276480138367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_55 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (2054703633393 / 2500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138242073079 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨55, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (2054703633393 / 2500000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138242073079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_56 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82154433358651 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138244087997 / 50000000000000 : ℝ))
      (E := (cell12504 ⟨56, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82154433358651 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (1138244087997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_57 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82120744644999 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227649216531 / 10000000000000 : ℝ))
      (E := (cell12504 ⟨57, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82120744644999 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (227649216531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_58 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82087079167093 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276496169539 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨58, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82087079167093 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276496169539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12504_59 : CellCertificate 12504 (892248566770871 / 10000000000000000 : ℝ) (419956353086159 / 250000000000000000 : ℝ) (67889242596427 / 2000000000000000 : ℝ)
    (cell12504 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · norm_num [cell12504]
  · have h := gap_lower (n := 12504) (a := (82053436897397 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276500184831 / 100000000000000 : ℝ))
      (E := (cell12504 ⟨59, by decide⟩).energy) (xi := (67889242596427 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12504 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12504]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12504])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12504) (a := (82053436897397 / 100000000000000 : ℝ)) (b := (164763497157 / 100000000000000 : ℝ)) (q := (2276500184831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12504])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12504]

theorem cert12505_40 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82696633004749 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276293435693 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨40, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82696633004749 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276293435693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_41 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82662568969383 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276297403177 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨41, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82662568969383 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276297403177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_42 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82628528629211 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138150709851 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨42, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82628528629211 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138150709851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_43 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82594511954393 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276305426021 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨43, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82594511954393 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276305426021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_44 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41280259457619 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276309421399 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨44, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41280259457619 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276309421399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_45 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (20631637370551 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569078351221 / 25000000000000 : ℝ))
      (E := (cell12505 ⟨45, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (20631637370551 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (569078351221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_46 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82492603625901 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276317434171 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨46, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82492603625901 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276317434171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_47 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82458681317083 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (28454017377 / 1250000000000 : ℝ))
      (E := (cell12505 ⟨47, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82458681317083 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (28454017377 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_48 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41212391263327 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (91053017917 / 4000000000000 : ℝ))
      (E := (cell12505 ⟨48, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41212391263327 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (91053017917 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_49 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82390907225663 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227632942897 / 10000000000000 : ℝ))
      (E := (cell12505 ⟨49, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82390907225663 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (227632942897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_50 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41178527692653 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276333449119 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨50, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41178527692653 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276333449119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_51 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41161613488461 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284542180901 / 12500000000000 : ℝ))
      (E := (cell12505 ⟨51, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41161613488461 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (284542180901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_52 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41144710985997 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276341420781 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨52, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41144710985997 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276341420781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_53 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (20563910085537 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138172713101 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨53, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (20563910085537 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138172713101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_54 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82221882059153 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138174700801 / 50000000000000 : ℝ))
      (E := (cell12505 ⟨54, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82221882059153 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (1138174700801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_55 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (41094073547459 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276353462053 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨55, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (41094073547459 / 50000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276353462053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_56 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82154435421493 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276357427081 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨56, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82154435421493 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276357427081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_57 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (82120747011069 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276361411363 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨57, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (82120747011069 / 100000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276361411363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_58 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (20521770458993 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276365411253 / 100000000000000 : ℝ))
      (E := (cell12505 ⟨58, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (20521770458993 / 25000000000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (2276365411253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12505_59 : CellCertificate 12505 (446109892299859 / 5000000000000000 : ℝ) (1679691035188747 / 1000000000000000000 : ℝ) (84854595256113 / 2500000000000000 : ℝ)
    (cell12505 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · norm_num [cell12505]
  · have h := gap_lower (n := 12505) (a := (320521249487 / 390625000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (142273088931 / 6250000000000 : ℝ))
      (E := (cell12505 ⟨59, by decide⟩).energy) (xi := (84854595256113 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12505 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12505]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12505])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12505) (a := (320521249487 / 390625000000 : ℝ)) (b := (41187538647 / 25000000000000 : ℝ)) (q := (142273088931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12505])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12505]

theorem cert12506_40 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82696630159639 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138081370661 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨40, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82696630159639 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138081370661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_41 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41331283217113 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276166751333 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨41, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41331283217113 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276166751333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_42 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82628526403579 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (56904268809 / 2500000000000 : ℝ))
      (E := (cell12506 ⟨42, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82628526403579 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (56904268809 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_43 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82594510037859 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455234948777 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨43, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82594510037859 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455234948777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_44 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41280258653687 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569044681293 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨44, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41280258653687 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569044681293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_45 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (16505309636517 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276182754113 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨45, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (16505309636517 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276182754113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_46 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (824926026341 / 1000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276186770737 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨46, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (824926026341 / 1000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276186770737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_47 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82458680632677 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284523846707 / 12500000000000 : ℝ))
      (E := (cell12506 ⟨47, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82458680632677 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284523846707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_48 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41212391074609 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455238952253 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨48, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41212391074609 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455238952253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_49 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (10298863394347 / 12500000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455239746349 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨49, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (10298863394347 / 12500000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455239746349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_50 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (1286828994071 / 1562500000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569050685507 / 25000000000000 : ℝ))
      (E := (cell12506 ⟨50, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (1286828994071 / 1562500000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (569050685507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_51 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (10290403439733 / 12500000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (45524134619 / 2000000000000 : ℝ))
      (E := (cell12506 ⟨51, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (10290403439733 / 12500000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (45524134619 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_52 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41144711409109 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284526344383 / 12500000000000 : ℝ))
      (E := (cell12506 ⟨52, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41144711409109 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (284526344383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_53 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (20563910373309 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276214752733 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨53, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (20563910373309 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276214752733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_54 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (20555470878671 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276218780137 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨54, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (20555470878671 / 25000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276218780137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_55 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41094074427237 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (227622277517 / 10000000000000 : ℝ))
      (E := (cell12506 ⟨55, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41094074427237 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (227622277517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_56 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (5134652342791 / 6250000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138113396819 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨56, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (5134652342791 / 6250000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138113396819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_57 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (41060374688711 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276230772971 / 100000000000000 : ℝ))
      (E := (cell12506 ⟨57, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (41060374688711 / 50000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (2276230772971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_58 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (82087084505099 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455246953721 / 20000000000000 : ℝ))
      (E := (cell12506 ⟨58, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (82087084505099 / 100000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (455246953721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12506_59 : CellCertificate 12506 (892191006854923 / 10000000000000000 : ℝ) (839778339765031 / 500000000000000000 : ℝ) (339390553713929 / 10000000000000000 : ℝ)
    (cell12506 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · norm_num [cell12506]
  · have h := gap_lower (n := 12506) (a := (16410688568031 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138119388343 / 50000000000000 : ℝ))
      (E := (cell12506 ⟨59, by decide⟩).energy) (xi := (339390553713929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12506 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12506]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12506])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12506) (a := (16410688568031 / 20000000000000 : ℝ)) (b := (823684071 / 500000000000 : ℝ)) (q := (1138119388343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12506])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12506]

theorem cert12507_40 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41348313657727 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276032102321 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨40, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41348313657727 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276032102321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_41 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20665640974989 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227603609617 / 10000000000000 : ℝ))
      (E := (cell12507 ⟨41, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20665640974989 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (227603609617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_42 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20657131044699 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138020070257 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨42, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20657131044699 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138020070257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_43 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41297254061067 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (569011029327 / 25000000000000 : ℝ))
      (E := (cell12507 ⟨43, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41297254061067 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (569011029327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_44 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41280257850141 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276048143389 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨44, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41280257850141 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276048143389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_45 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82526546883699 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276052100181 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨45, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82526546883699 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276052100181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_46 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20623150410749 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (113802805209 / 5000000000000 : ℝ))
      (E := (cell12507 ⟨46, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20623150410749 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (113802805209 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_47 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82458679948929 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276060154067 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨47, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82458679948929 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276060154067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_48 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20606195443101 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (91042565219 / 4000000000000 : ℝ))
      (E := (cell12507 ⟨48, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20606195443101 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (91042565219 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_49 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82390907084471 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138034074697 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨49, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82390907084471 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138034074697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_50 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82357055856327 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276072149897 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨50, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82357055856327 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276072149897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_51 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82323228059313 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (284509516217 / 12500000000000 : ℝ))
      (E := (cell12507 ⟨51, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82323228059313 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (284509516217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_52 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41144711832457 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (284510018183 / 12500000000000 : ℝ))
      (E := (cell12507 ⟨52, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41144711832457 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (284510018183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_53 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20563910661189 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138042067723 / 50000000000000 : ℝ))
      (E := (cell12507 ⟨53, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20563910661189 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (1138042067723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_54 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82221884970611 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455217631171 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨54, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82221884970611 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455217631171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_55 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (20547037653597 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276092144591 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨55, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (20547037653597 / 25000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276092144591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_56 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (4107721977407 / 5000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455219231491 / 20000000000000 : ℝ))
      (E := (cell12507 ⟨56, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (4107721977407 / 5000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (455219231491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_57 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (41060375872029 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276100131879 / 100000000000000 : ℝ))
      (E := (cell12507 ⟨57, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (41060375872029 / 50000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (2276100131879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_58 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (82087087174471 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (142256511403 / 6250000000000 : ℝ))
      (E := (cell12507 ⟨58, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (82087087174471 / 100000000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (142256511403 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12507_59 : CellCertificate 12507 (446081116767709 / 5000000000000000 : ℝ) (1679422345363421 / 1000000000000000000 : ℝ) (339362731049279 / 10000000000000000 : ℝ)
    (cell12507 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · norm_num [cell12507]
  · have h := gap_lower (n := 12507) (a := (10256680726481 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (569027031963 / 25000000000000 : ℝ))
      (E := (cell12507 ⟨59, by decide⟩).energy) (xi := (339362731049279 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12507 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12507]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12507])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12507) (a := (10256680726481 / 12500000000000 : ℝ)) (b := (20590434499 / 12500000000000 : ℝ)) (q := (569027031963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12507])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12507]

theorem cert12508_40 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82696624472193 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (113795078871 / 5000000000000 : ℝ))
      (E := (cell12508 ⟨40, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82696624472193 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (113795078871 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_41 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20665640341643 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284488194399 / 12500000000000 : ℝ))
      (E := (cell12508 ⟨41, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20665640341643 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284488194399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_42 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (4131426097743 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568977381347 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨42, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (4131426097743 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568977381347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_43 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (4129725310361 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275913546289 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨43, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (4129725310361 / 5000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275913546289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_44 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41280257046981 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568979389601 / 25000000000000 : ℝ))
      (E := (cell12508 ⟨44, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41280257046981 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (568979389601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_45 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20631636396387 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275921560777 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨45, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20631636396387 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275921560777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_46 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (20623150163147 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275925552237 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨46, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (20623150163147 / 25000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275925552237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_47 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (1030733490823 / 1250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2222587433 / 97656250000 : ℝ))
      (E := (cell12508 ⟨47, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (1030733490823 / 1250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2222587433 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_48 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (8242478139621 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137966777777 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨48, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (8242478139621 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137966777777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_49 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (329563628059 / 400000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275937564033 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨49, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (329563628059 / 400000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275937564033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_50 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (5147316005791 / 6250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (455188310959 / 20000000000000 : ℝ))
      (E := (cell12508 ⟨50, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (5147316005791 / 6250000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (455188310959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_51 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82323228601271 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137972792289 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨51, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82323228601271 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137972792289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_52 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82289424512079 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275949591983 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨52, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82289424512079 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275949591983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_53 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (8225564379671 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275953574337 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨53, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (8225564379671 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275953574337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_54 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82221886426933 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284494698477 / 12500000000000 : ℝ))
      (E := (cell12508 ⟨54, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82221886426933 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284494698477 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_55 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (82188152374661 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (455192314063 / 20000000000000 : ℝ))
      (E := (cell12508 ⟨55, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (82188152374661 / 100000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (455192314063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_56 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (16430888322389 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137982788819 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨56, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (16430888322389 / 20000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137982788819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_57 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (41060377055489 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137984803171 / 50000000000000 : ℝ))
      (E := (cell12508 ⟨57, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (41060377055489 / 50000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (1137984803171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_58 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (8208708984409 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275973593627 / 100000000000000 : ℝ))
      (E := (cell12508 ⟨58, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (8208708984409 / 10000000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (2275973593627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12508_59 : CellCertificate 12508 (223033366160033 / 2500000000000000 : ℝ) (1679288032683669 / 1000000000000000000 : ℝ) (67866982605843 / 2000000000000000 : ℝ)
    (cell12508 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · norm_num [cell12508]
  · have h := gap_lower (n := 12508) (a := (65642759027 / 80000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284497199343 / 12500000000000 : ℝ))
      (E := (cell12508 ⟨59, by decide⟩).energy) (xi := (67866982605843 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12508 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12508]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12508])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12508) (a := (65642759027 / 80000000000 : ℝ)) (b := (32942027993 / 20000000000000 : ℝ)) (q := (284497199343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12508])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12508]

theorem cert12509_40 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (2584269425933 / 3125000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137885524581 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨40, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (2584269425933 / 3125000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137885524581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_41 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82662558834073 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275775010897 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨41, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82662558834073 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275775010897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_42 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82628519731773 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455155804907 / 20000000000000 : ℝ))
      (E := (cell12509 ⟨42, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82628519731773 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455155804907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_43 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (20648626073279 / 25000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275783030829 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨43, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (20648626073279 / 25000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275783030829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_44 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41280256244207 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275787029041 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨44, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41280256244207 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275787029041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_45 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82526544288131 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275791018213 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨45, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82526544288131 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275791018213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_46 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (20623149915719 / 25000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137897528021 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨46, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (20623149915719 / 25000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137897528021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_47 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82458678583409 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275799023421 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨47, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82458678583409 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275799023421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_48 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82424781020637 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455160607301 / 20000000000000 : ℝ))
      (E := (cell12509 ⟨48, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82424781020637 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (455160607301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_49 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82390906945611 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275807034607 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨49, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82390906945611 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275807034607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_50 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (8235705632953 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275811015689 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨50, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (8235705632953 / 10000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275811015689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_51 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (10290403642967 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227581503649 / 10000000000000 : ℝ))
      (E := (cell12509 ⟨51, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (10290403642967 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (227581503649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_52 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (41144712679857 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568954758903 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨52, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (41144712679857 / 50000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568954758903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_53 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (10281955618637 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275823069411 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨53, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (10281955618637 / 12500000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275823069411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_54 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (1644437757673 / 2000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275827076021 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨54, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (1644437757673 / 2000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275827076021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_55 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82188154135291 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137915526173 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨55, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82188154135291 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137915526173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_56 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82154443676071 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275835054187 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨56, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82154443676071 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275835054187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_57 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82120756478181 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137919539053 / 50000000000000 : ℝ))
      (E := (cell12509 ⟨57, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82120756478181 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (1137919539053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_58 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (16417418502791 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275843061297 / 100000000000000 : ℝ))
      (E := (cell12509 ⟨58, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (16417418502791 / 20000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (2275843061297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12509_59 : CellCertificate 12509 (892104700167997 / 10000000000000000 : ℝ) (33583074829713 / 20000000000000000 : ℝ) (339307099652453 / 10000000000000000 : ℝ)
    (cell12509 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · norm_num [cell12509]
  · have h := gap_lower (n := 12509) (a := (82053451755861 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568961764753 / 25000000000000 : ℝ))
      (E := (cell12509 ⟨59, by decide⟩).energy) (xi := (339307099652453 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12509 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12509]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12509])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12509) (a := (82053451755861 / 100000000000000 : ℝ)) (b := (164696806117 / 100000000000000 : ℝ)) (q := (568961764753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12509])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12509]

theorem cert12510_40 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82696618788443 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137820288139 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨40, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82696618788443 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137820288139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_41 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82662556302461 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227564458079 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨41, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82662556302461 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227564458079 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_42 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82628517509533 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275648579181 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨42, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82628517509533 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275648579181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_43 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82594502379821 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275652570931 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨43, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82594502379821 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275652570931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_44 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41280255441819 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275656555301 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨44, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41280255441819 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275656555301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_45 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82526542991447 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137830265667 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨45, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82526542991447 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137830265667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_46 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (4124629933693 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (91026582269 / 4000000000000 : ℝ))
      (E := (cell12510 ⟨46, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (4124629933693 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (91026582269 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_47 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82458677901637 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137834285629 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨47, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82458677901637 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137834285629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_48 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20606195161421 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227567257333 / 10000000000000 : ℝ))
      (E := (cell12510 ⟨48, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20606195161421 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (227567257333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_49 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (16478181375411 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455135312223 / 20000000000000 : ℝ))
      (E := (cell12510 ⟨49, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (16478181375411 / 20000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (455135312223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_50 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82357056566949 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (284460073943 / 12500000000000 : ℝ))
      (E := (cell12510 ⟨50, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82357056566949 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (284460073943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_51 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20580807421677 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137842272231 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨51, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20580807421677 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137842272231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_52 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (4114471310391 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275688594371 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨52, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (4114471310391 / 5000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275688594371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_53 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41127823050957 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137846280817 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨53, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41127823050957 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137846280817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_54 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82221889340763 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568924140353 / 25000000000000 : ℝ))
      (E := (cell12510 ⟨54, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82221889340763 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (568924140353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_55 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82188155896279 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275700590683 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨55, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82188155896279 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275700590683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_56 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20538611435129 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137852293553 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨56, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20538611435129 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137852293553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_57 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (20530189711417 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275708606299 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨57, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (20530189711417 / 25000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275708606299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_58 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (41043547592033 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275712585459 / 100000000000000 : ℝ))
      (E := (cell12510 ⟨58, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (41043547592033 / 50000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (2275712585459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12510_59 : CellCertificate 12510 (111509492514743 / 1250000000000000 : ℝ) (1679019471764211 / 1000000000000000000 : ℝ) (84819822729427 / 2500000000000000 : ℝ)
    (cell12510 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · norm_num [cell12510]
  · have h := gap_lower (n := 12510) (a := (82053454728181 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137858289917 / 50000000000000 : ℝ))
      (E := (cell12510 ⟨59, by decide⟩).energy) (xi := (84819822729427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12510 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12510]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12510])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12510) (a := (82053454728181 / 100000000000000 : ℝ)) (b := (10292717153 / 6250000000000 : ℝ)) (q := (1137858289917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12510])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12510]

theorem cert12511_40 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82696615947953 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56887752501 / 2500000000000 : ℝ))
      (E := (cell12511 ⟨40, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82696615947953 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56887752501 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_41 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41331276885867 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (284439268421 / 12500000000000 : ℝ))
      (E := (cell12511 ⟨41, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41331276885867 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (284439268421 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_42 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82628515288141 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275518130551 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨42, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82628515288141 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275518130551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_43 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (10324312558417 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568880526949 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨43, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (10324312558417 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568880526949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_44 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82560509279633 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275526137187 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨44, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82560509279633 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275526137187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_45 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82526541695497 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275530158989 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨45, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82526541695497 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275530158989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_46 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (4124629884277 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275534113157 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨46, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (4124629884277 / 5000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275534113157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_47 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41229338610261 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455107623203 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨47, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41229338610261 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455107623203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_48 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (10303097533919 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227554210711 / 10000000000000 : ℝ))
      (E := (cell12511 ⟨48, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (10303097533919 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227554210711 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_49 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41195453404541 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56888653589 / 2500000000000 : ℝ))
      (E := (cell12511 ⟨49, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41195453404541 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (56888653589 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_50 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82357056804913 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275550164433 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨50, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82357056804913 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275550164433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_51 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (20580807557547 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137777083741 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨51, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (20580807557547 / 25000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137777083741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_52 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16457885411279 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137779075121 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨52, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16457885411279 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137779075121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_53 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (16451129451033 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (91022486763 / 4000000000000 : ℝ))
      (E := (cell12511 ⟨53, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (16451129451033 / 20000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (91022486763 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_54 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (8222189079827 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568891540527 / 25000000000000 : ℝ))
      (E := (cell12511 ⟨54, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (8222189079827 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (568891540527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_55 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (10273519707203 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137785063123 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨55, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (10273519707203 / 12500000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137785063123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_56 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41077223902641 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455114835279 / 20000000000000 : ℝ))
      (E := (cell12511 ⟨56, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41077223902641 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (455114835279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_57 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (41060380606719 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137789065897 / 50000000000000 : ℝ))
      (E := (cell12511 ⟨57, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (41060380606719 / 50000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (1137789065897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_58 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (82087097854423 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275582166113 / 100000000000000 : ℝ))
      (E := (cell12511 ⟨58, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (82087097854423 / 100000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (2275582166113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12511_59 : CellCertificate 12511 (111505898061113 / 1250000000000000 : ℝ) (1678885223514201 / 1000000000000000000 : ℝ) (67850297364739 / 2000000000000000 : ℝ)
    (cell12511 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · norm_num [cell12511]
  · have h := gap_lower (n := 12511) (a := (8205345770071 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227558615721 / 10000000000000 : ℝ))
      (E := (cell12511 ⟨59, by decide⟩).energy) (xi := (67850297364739 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12511 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12511]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12511])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12511) (a := (8205345770071 / 10000000000000 : ℝ)) (b := (164670144957 / 100000000000000 : ℝ)) (q := (227558615721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12511])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12511]

theorem cert12512_40 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82696613108387 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137689868953 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨40, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82696613108387 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137689868953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_41 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20665637810473 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (455076753877 / 20000000000000 : ℝ))
      (E := (cell12512 ⟨41, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20665637810473 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (455076753877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_42 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (16525702613519 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137693868711 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨42, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (16525702613519 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137693868711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_43 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82594498555659 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (142211984939 / 6250000000000 : ℝ))
      (E := (cell12512 ⟨43, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82594498555659 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (142211984939 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_44 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (206401269191 / 250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275395774697 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨44, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (206401269191 / 250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275395774697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_45 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82526540400281 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137699862319 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨45, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82526540400281 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137699862319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_46 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (16498519339583 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275403725339 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨46, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (16498519339583 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275403725339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_47 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (16491735308013 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137703887739 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨47, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (16491735308013 / 20000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137703887739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_48 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82424779897639 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137705877841 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨48, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82424779897639 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137705877841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_49 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82390906741691 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275415781941 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨49, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82390906741691 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275415781941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_50 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82357057043421 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275419734357 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨50, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82357057043421 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275419734357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_51 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (3292929230967 / 4000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137711893787 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨51, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (3292929230967 / 4000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137711893787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_52 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (514308924409 / 625000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568856940559 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨52, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (514308924409 / 625000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568856940559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_53 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (5140978025553 / 6250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137715886833 / 50000000000000 : ℝ))
      (E := (cell12512 ⟨53, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (5140978025553 / 6250000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (1137715886833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_54 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (20555473064043 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (284429469999 / 12500000000000 : ℝ))
      (E := (cell12512 ⟨54, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (20555473064043 / 25000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (284429469999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_55 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82188159419327 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275439777199 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨55, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82188159419327 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275439777199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_56 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (2567326558449 / 3125000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275443762947 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨56, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (2567326558449 / 3125000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275443762947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_57 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (8212076358149 / 10000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568861943213 / 25000000000000 : ℝ))
      (E := (cell12512 ⟨57, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (8212076358149 / 10000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (568861943213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_58 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (41043550262513 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275451803261 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨58, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (41043550262513 / 50000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275451803261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12512_59 : CellCertificate 12512 (892018433279809 / 10000000000000000 : ℝ) (167875099673047 / 100000000000000000 : ℝ) (339223687369131 / 10000000000000000 : ℝ)
    (cell12512 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · norm_num [cell12512]
  · have h := gap_lower (n := 12512) (a := (82053460673447 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275455791141 / 100000000000000 : ℝ))
      (E := (cell12512 ⟨59, by decide⟩).energy) (xi := (339223687369131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12512 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12512]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12512])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12512) (a := (82053460673447 / 100000000000000 : ℝ)) (b := (41164204411 / 25000000000000 : ℝ)) (q := (2275455791141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12512])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12512]

theorem cert12513_40 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (5168538141859 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568812357787 / 25000000000000 : ℝ))
      (E := (cell12513 ⟨40, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (5168538141859 / 6250000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (568812357787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_41 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (16532509742587 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (56881336171 / 2500000000000 : ℝ))
      (E := (cell12513 ⟨41, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (16532509742587 / 20000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (56881336171 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_42 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82628510847897 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142203587487 / 6250000000000 : ℝ))
      (E := (cell12513 ⟨42, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82628510847897 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142203587487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_43 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (10324312080599 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455052281403 / 20000000000000 : ℝ))
      (E := (cell12513 ⟨43, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (10324312080599 / 12500000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455052281403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_44 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82560506073937 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275265409011 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨44, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82560506073937 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275265409011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_45 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82526539105797 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137634702411 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨45, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82526539105797 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137634702411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_46 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41246297855493 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137636726071 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨46, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41246297855493 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137636726071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_47 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41229337930133 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275277431859 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨47, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41229337930133 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275277431859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_48 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41212389762273 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275281401213 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨48, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41212389762273 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275281401213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_49 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41195453337441 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137642708659 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨49, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41195453337441 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137642708659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_50 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41178528641237 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455057883849 / 20000000000000 : ℝ))
      (E := (cell12513 ⟨50, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41178528641237 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (455057883849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_51 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82323231318669 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275293404739 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨51, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82323231318669 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275293404739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_52 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41144714377477 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142206089397 / 6250000000000 : ℝ))
      (E := (cell12513 ⟨52, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41144714377477 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142206089397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_53 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82255649562963 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137650717221 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨53, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82255649562963 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137650717221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_54 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82221893714469 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137652707061 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨54, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82221893714469 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137652707061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_55 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (20547040295347 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137654712689 / 50000000000000 : ℝ))
      (E := (cell12513 ⟨55, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (20547040295347 / 25000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (1137654712689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_56 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41077225967887 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142207091561 / 6250000000000 : ℝ))
      (E := (cell12513 ⟨56, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41077225967887 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (142207091561 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_57 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (3284830637993 / 4000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275317470341 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨57, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (3284830637993 / 4000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275317470341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_58 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (41043551597937 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (9101285751 / 400000000000 : ℝ))
      (E := (cell12513 ⟨58, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (41043551597937 / 50000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (9101285751 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12513_59 : CellCertificate 12513 (111498710811199 / 1250000000000000 : ℝ) (1678616791407869 / 1000000000000000000 : ℝ) (84798973138183 / 2500000000000000 : ℝ)
    (cell12513 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · norm_num [cell12513]
  · have h := gap_lower (n := 12513) (a := (82053463646393 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275325422451 / 100000000000000 : ℝ))
      (E := (cell12513 ⟨59, by decide⟩).energy) (xi := (84798973138183 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12513 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12513]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12513])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12513) (a := (82053463646393 / 100000000000000 : ℝ)) (b := (164643492509 / 100000000000000 : ℝ)) (q := (2275325422451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12513])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12513]

theorem cert12514_40 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82696607432023 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275119121039 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨40, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82696607432023 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275119121039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_41 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82662546184863 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275123120983 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨41, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82662546184863 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275123120983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_42 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16525701725809 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275127117667 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨42, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16525701725809 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275127117667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_43 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82594494734733 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568782777643 / 25000000000000 : ℝ))
      (E := (cell12514 ⟨43, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82594494734733 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (568782777643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_44 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16512100894449 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142195947361 / 6250000000000 : ℝ))
      (E := (cell12514 ⟨44, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16512100894449 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142195947361 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_45 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41263268906023 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137569570349 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨45, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41263268906023 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137569570349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_46 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82492594724751 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137571558479 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨46, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82492594724751 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137571558479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_47 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82458675181123 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275147144057 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨47, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82458675181123 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275147144057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_48 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (10303097394009 / 12500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137575580769 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨48, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (10303097394009 / 12500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137575580769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_49 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41195453304327 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275155167577 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨49, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41195453304327 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275155167577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_50 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82357057522071 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137579580067 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨50, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82357057522071 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137579580067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_51 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82323231863669 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275163136957 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨51, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82323231863669 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275163136957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_52 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (41144714802469 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137583577297 / 50000000000000 : ℝ))
      (E := (cell12514 ⟨52, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (41144714802469 / 50000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (1137583577297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_53 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (8225565071751 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455034230281 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨53, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (8225565071751 / 10000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455034230281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_54 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (2055547379329 / 2500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275175183561 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨54, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (2055547379329 / 2500000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275175183561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_55 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (16437632588761 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275179129869 / 100000000000000 : ℝ))
      (E := (cell12514 ⟨55, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (16437632588761 / 20000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (2275179129869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_56 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (164308908003 / 200000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142198947767 / 6250000000000 : ℝ))
      (E := (cell12514 ⟨56, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (164308908003 / 200000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142198947767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_57 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82120768318443 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455037433027 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨57, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82120768318443 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455037433027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_58 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82087105866967 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142199449243 / 6250000000000 : ℝ))
      (E := (cell12514 ⟨58, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82087105866967 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (142199449243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12514_59 : CellCertificate 12514 (178392188823437 / 2000000000000000 : ℝ) (419620651885313 / 250000000000000000 : ℝ) (339168102373217 / 10000000000000000 : ℝ)
    (cell12514 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · norm_num [cell12514]
  · have h := gap_lower (n := 12514) (a := (82053466619547 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455039033899 / 20000000000000 : ℝ))
      (E := (cell12514 ⟨59, by decide⟩).energy) (xi := (339168102373217 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12514 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12514]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12514])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12514) (a := (82053466619547 / 100000000000000 : ℝ)) (b := (3292603391 / 2000000000000 : ℝ)) (q := (455039033899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12514])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12514]

theorem cert12515_40 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (3307864183809 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137494462519 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨40, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (3307864183809 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137494462519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_41 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (3306501746307 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274992909319 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨41, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (3306501746307 / 4000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2274992909319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_42 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82628506411039 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137498445523 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨42, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82628506411039 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137498445523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_43 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82594492825483 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137500464247 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨43, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82594492825483 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137500464247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_44 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82560502871323 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275004903347 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨44, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82560502871323 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275004903347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_45 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (20631634129757 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275008932263 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨45, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (20631634129757 / 25000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275008932263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_46 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82492593739211 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275012896397 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨46, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82492593739211 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275012896397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_47 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41229337251319 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568754228017 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨47, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41229337251319 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568754228017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_48 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41212389390109 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137510459411 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨48, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41212389390109 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137510459411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_49 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82390906543009 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (142189057177 / 6250000000000 : ℝ))
      (E := (cell12515 ⟨49, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82390906543009 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (142189057177 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_50 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82357057762213 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137514449029 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨50, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82357057762213 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137514449029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_51 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (10290404051147 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137516462619 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨51, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (10290404051147 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137516462619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_52 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (8228943045539 / 10000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137518467481 / 50000000000000 : ℝ))
      (E := (cell12515 ⟨52, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (8228943045539 / 10000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (1137518467481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_53 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (10281956484061 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568760231139 / 25000000000000 : ℝ))
      (E := (cell12515 ⟨53, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (10281956484061 / 12500000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (568760231139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_54 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (16444379326449 / 20000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275044891131 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨54, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (16444379326449 / 20000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275044891131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_55 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82188164706579 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275048949753 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨55, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82188164706579 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275048949753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_56 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41077228033773 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (113752645997 / 5000000000000 : ℝ))
      (E := (cell12515 ⟨56, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41077228033773 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (113752645997 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_57 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82120770687343 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275056916363 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨57, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82120770687343 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275056916363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_58 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (41043554269153 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275060935369 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨58, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (41043554269153 / 50000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275060935369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12515_59 : CellCertificate 12515 (445966103080761 / 5000000000000000 : ℝ) (839174222562737 / 500000000000000000 : ℝ) (42392539603663 / 1250000000000000 : ℝ)
    (cell12515 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · norm_num [cell12515]
  · have h := gap_lower (n := 12515) (a := (82053469592909 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275064913921 / 100000000000000 : ℝ))
      (E := (cell12515 ⟨59, by decide⟩).energy) (xi := (42392539603663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12515 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12515]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12515])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12515) (a := (82053469592909 / 100000000000000 : ℝ)) (b := (1286069131 / 781250000000 : ℝ)) (q := (2275064913921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12515])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12515]

theorem cert12516_40 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82696601759349 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284357340711 / 12500000000000 : ℝ))
      (E := (cell12516 ⟨40, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82696601759349 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284357340711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_41 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82662541131371 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137431347173 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨41, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82662541131371 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137431347173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_42 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82628504193879 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227486671993 / 10000000000000 : ℝ))
      (E := (cell12516 ⟨42, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82628504193879 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227486671993 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_43 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (1032431136463 / 1250000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137435342193 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨43, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (1032431136463 / 1250000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137435342193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_44 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (20640125317793 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137437352273 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨44, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (20640125317793 / 25000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137437352273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_45 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41263267613371 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137439360337 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨45, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41263267613371 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137439360337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_46 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41246296377183 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227488273159 / 10000000000000 : ℝ))
      (E := (cell12516 ⟨46, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41246296377183 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227488273159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_47 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82458673824809 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137443367949 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨47, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82458673824809 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137443367949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_48 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82424778408983 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137445365993 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨48, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82424778408983 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137445365993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_49 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (16478181295589 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274894718029 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨49, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (16478181295589 / 20000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274894718029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_50 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41178529001449 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284362343869 / 12500000000000 : ℝ))
      (E := (cell12516 ⟨50, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41178529001449 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (284362343869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_51 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82323232955189 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (568725677649 / 25000000000000 : ℝ))
      (E := (cell12516 ⟨51, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82323232955189 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (568725677649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_52 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82289431306311 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137453356223 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨52, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82289431306311 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137453356223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_53 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41127826513949 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454982150779 / 20000000000000 : ℝ))
      (E := (cell12516 ⟨53, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41127826513949 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454982150779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_54 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (3288875923669 / 4000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227491471401 / 10000000000000 : ℝ))
      (E := (cell12516 ⟨54, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (3288875923669 / 4000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (227491471401 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_55 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (8218816646971 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454983741557 / 20000000000000 : ℝ))
      (E := (cell12516 ⟨55, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (8218816646971 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (454983741557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_56 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82154458133911 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274922731983 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨56, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82154458133911 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274922731983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_57 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (41060386528263 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274926724027 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨57, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (41060386528263 / 50000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274926724027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_58 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (8208711120989 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274930739347 / 100000000000000 : ℝ))
      (E := (cell12516 ⟨58, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (8208711120989 / 10000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (2274930739347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12516_59 : CellCertificate 12516 (178380694524307 / 2000000000000000 : ℝ) (1678214304155391 / 1000000000000000000 : ℝ) (10597266747491 / 312500000000000 : ℝ)
    (cell12516 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · norm_num [cell12516]
  · have h := gap_lower (n := 12516) (a := (82053472566479 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137467387041 / 50000000000000 : ℝ))
      (E := (cell12516 ⟨59, by decide⟩).energy) (xi := (10597266747491 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12516 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12516]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12516])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12516) (a := (82053472566479 / 100000000000000 : ℝ)) (b := (164603530161 / 100000000000000 : ℝ)) (q := (1137467387041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12516])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12516]

theorem cert12517_40 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (16539319784879 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274728581719 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨40, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (16539319784879 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274728581719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_41 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82662538605951 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274732593569 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨41, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82662538605951 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274732593569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_42 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41314250988783 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137368272771 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨42, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41314250988783 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137368272771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_43 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41297244504703 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (454948110929 / 20000000000000 : ℝ))
      (E := (cell12517 ⟨43, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41297244504703 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (454948110929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_44 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (8256049967179 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137372280689 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨44, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (8256049967179 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137372280689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_45 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (20631633483797 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274748564779 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨45, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (20631633483797 / 25000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274748564779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_46 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (16498518354043 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568688140917 / 25000000000000 : ℝ))
      (E := (cell12517 ⟨46, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (16498518354043 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (568688140917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_47 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82458673147637 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (45495131133 / 2000000000000 : ℝ))
      (E := (cell12517 ⟨47, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82458673147637 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (45495131133 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_48 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41212389019183 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274760601031 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨48, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41212389019183 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274760601031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_49 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41195453206731 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274764577169 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨49, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41195453206731 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274764577169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_50 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41178529122063 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137384300443 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨50, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41178529122063 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137384300443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_51 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82323233501709 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274772611007 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨51, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82323233501709 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274772611007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_52 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82289432157701 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274776605069 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨52, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82289432157701 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274776605069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_53 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82255654183739 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (227478058039 / 10000000000000 : ℝ))
      (E := (cell12517 ⟨53, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82255654183739 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (227478058039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_54 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (41110949775799 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137392296571 / 50000000000000 : ℝ))
      (E := (cell12517 ⟨54, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (41110949775799 / 50000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (1137392296571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_55 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82188168233197 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274788581213 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨55, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82188168233197 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274788581213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_56 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (16430892040119 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274792600401 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨56, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (16430892040119 / 20000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274792600401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_57 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (8212077542599 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274796588129 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨57, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (8212077542599 / 10000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274796588129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_58 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82087113881719 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (142175037489 / 6250000000000 : ℝ))
      (E := (cell12517 ⟨58, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82087113881719 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (142175037489 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12517_59 : CellCertificate 12517 (891874743496159 / 10000000000000000 : ℝ) (1678080184625863 / 1000000000000000000 : ℝ) (8477118991079 / 250000000000000 : ℝ)
    (cell12517 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · norm_num [cell12517]
  · have h := gap_lower (n := 12517) (a := (82053475540257 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274804631627 / 100000000000000 : ℝ))
      (E := (cell12517 ⟨59, by decide⟩).energy) (xi := (8477118991079 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12517 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12517]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12517])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12517) (a := (82053475540257 / 100000000000000 : ℝ)) (b := (164590213729 / 100000000000000 : ℝ)) (q := (2274804631627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12517])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12517]

theorem cert12518_40 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82696596090363 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274598493133 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨40, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82696596090363 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274598493133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_41 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (16532507216283 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454920497897 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨41, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (16532507216283 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454920497897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_42 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82628499762097 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274606485441 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨42, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82628499762097 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274606485441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_43 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82594487102579 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137305240237 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨43, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82594487102579 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137305240237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_44 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41280249036589 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137307236921 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨44, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41280249036589 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137307236921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_45 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (16505306528873 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274618464579 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨45, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (16505306528873 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274618464579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_46 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41246295393379 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (18196980083 / 800000000000 : ℝ))
      (E := (cell12518 ⟨46, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41246295393379 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (18196980083 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_47 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82458672471121 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274626492117 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨47, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82458672471121 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274626492117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_48 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82424777668369 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137315233519 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨48, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82424777668369 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137315233519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_49 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (2059772658739 / 2500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568658623063 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨49, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (2059772658739 / 2500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568658623063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_50 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41178529242949 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (90985540273 / 4000000000000 : ℝ))
      (E := (cell12518 ⟨50, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41178529242949 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (90985540273 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_51 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (41161617024367 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274642508499 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨51, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (41161617024367 / 50000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274642508499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_52 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (2057235825239 / 2500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274646494809 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨52, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (2057235825239 / 2500000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274646494809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_53 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82255655340011 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274650522111 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨53, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82255655340011 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274650522111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_54 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (16444380202373 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137327264263 / 50000000000000 : ℝ))
      (E := (cell12518 ⟨54, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (16444380202373 / 20000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (1137327264263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_55 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82188169997041 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568664627739 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨55, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82188169997041 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568664627739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_56 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82154462267599 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454932505039 / 20000000000000 : ℝ))
      (E := (cell12518 ⟨56, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82154462267599 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (454932505039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_57 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82120777795737 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568666627167 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨57, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82120777795737 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568666627167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_58 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82087116553793 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274670516801 / 100000000000000 : ℝ))
      (E := (cell12518 ⟨58, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82087116553793 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (2274670516801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12518_59 : CellCertificate 12518 (891846018784327 / 10000000000000000 : ℝ) (419486521632937 / 250000000000000000 : ℝ) (10595530874949 / 312500000000000 : ℝ)
    (cell12518 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · norm_num [cell12518]
  · have h := gap_lower (n := 12518) (a := (82053478514243 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568668621639 / 25000000000000 : ℝ))
      (E := (cell12518 ⟨59, by decide⟩).energy) (xi := (10595530874949 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12518 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12518]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12518])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12518) (a := (82053478514243 / 100000000000000 : ℝ)) (b := (164576899471 / 100000000000000 : ℝ)) (q := (568668621639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12518])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12518]

theorem cert12519_40 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (20674148314313 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274468459929 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨40, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (20674148314313 / 25000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274468459929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_41 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41331266778881 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454894488169 / 20000000000000 : ℝ))
      (E := (cell12519 ⟨41, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41331266778881 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454894488169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_42 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41314248773737 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274476422069 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨42, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41314248773737 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274476422069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_43 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82594485196559 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137240230937 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨43, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82594485196559 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137240230937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_44 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (10320062059417 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274484441937 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨44, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (10320062059417 / 12500000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274484441937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_45 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (3301061254171 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (284311052509 / 12500000000000 : ℝ))
      (E := (cell12519 ⟨45, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (3301061254171 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (284311052509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_46 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41246294901997 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (142155778373 / 6250000000000 : ℝ))
      (E := (cell12519 ⟨46, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41246294901997 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (142155778373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_47 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82458671795261 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568624106127 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨47, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82458671795261 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568624106127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_48 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82424777298989 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568625111961 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨48, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82424777298989 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568625111961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_49 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41195453143119 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274504463279 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨49, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41195453143119 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274504463279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_50 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41178529364107 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (71078389649 / 3125000000000 : ℝ))
      (E := (cell12519 ⟨50, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41178529364107 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (71078389649 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_51 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (16464646919253 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274512462057 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨51, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (16464646919253 / 20000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274512462057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_52 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41144716930943 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274516440679 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨52, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41144716930943 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274516440679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_53 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41127828248357 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274520460987 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨53, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41127828248357 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274520460987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_54 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (3288876098901 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454904892221 / 20000000000000 : ℝ))
      (E := (cell12519 ⟨54, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (3288876098901 / 4000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (454904892221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_55 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82188171761241 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (227452843793 / 10000000000000 : ℝ))
      (E := (cell12519 ⟨55, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82188171761241 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (227452843793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_56 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82154464334921 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (113726622363 / 5000000000000 : ℝ))
      (E := (cell12519 ⟨56, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82154464334921 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (113726622363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_57 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (41060390082883 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568634121411 / 25000000000000 : ℝ))
      (E := (cell12519 ⟨57, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (41060390082883 / 50000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (568634121411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_58 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (320652809477 / 390625000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274540490277 / 100000000000000 : ℝ))
      (E := (cell12519 ⟨58, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (320652809477 / 390625000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (2274540490277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12519_59 : CellCertificate 12519 (445908649242487 / 5000000000000000 : ℝ) (419453002466977 / 250000000000000000 : ℝ) (339029220984057 / 10000000000000000 : ℝ)
    (cell12519 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · norm_num [cell12519]
  · have h := gap_lower (n := 12519) (a := (82053481488437 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137272228611 / 50000000000000 : ℝ))
      (E := (cell12519 ⟨59, by decide⟩).energy) (xi := (339029220984057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12519 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12519]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12519])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12519) (a := (82053481488437 / 100000000000000 : ℝ)) (b := (41140896847 / 25000000000000 : ℝ)) (q := (1137272228611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12519])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12519]

theorem cert12520_40 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41348295212531 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113716921169 / 5000000000000 : ℝ))
      (E := (cell12520 ⟨40, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41348295212531 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (113716921169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_41 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (5166408189687 / 6250000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568585611913 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨41, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (5166408189687 / 6250000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568585611913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_42 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (1291070239589 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274346414207 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨42, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (1291070239589 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274346414207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_43 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41297241645673 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137175220023 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨43, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41297241645673 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137175220023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_44 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82560494878263 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568588616417 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨44, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82560494878263 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568588616417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_45 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (20631632516229 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137179215631 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨45, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (20631632516229 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137179215631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_46 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (3299703552877 / 4000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137181226659 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨46, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (3299703552877 / 4000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137181226659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_47 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82458671120057 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137183235807 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨47, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82458671120057 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137183235807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_48 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (20606194232557 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142148151601 / 6250000000000 : ℝ))
      (E := (cell12520 ⟨48, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (20606194232557 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (142148151601 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_49 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41195453111749 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568593607827 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨49, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41195453111749 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568593607827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_50 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (1286829046423 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137189213877 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨50, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (1286829046423 / 1562500000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137189213877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_51 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41161617572151 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454876494337 / 20000000000000 : ℝ))
      (E := (cell12520 ⟨51, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41161617572151 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (454876494337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_52 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82289434714681 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274386442679 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨52, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82289434714681 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274386442679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_53 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82255657653847 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274390456057 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨53, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82255657653847 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274390456057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_54 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82221903933579 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137197224969 / 50000000000000 : ℝ))
      (E := (cell12520 ⟨54, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82221903933579 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (1137197224969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_55 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41094086762899 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274398480303 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨55, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41094086762899 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274398480303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_56 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (82154466402563 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (284300310601 / 12500000000000 : ℝ))
      (E := (cell12520 ⟨56, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (82154466402563 / 100000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (284300310601 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_57 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (20530195634019 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568601614983 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨57, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (20530195634019 / 25000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568601614983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_58 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (3283484875947 / 4000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274410461101 / 100000000000000 : ℝ))
      (E := (cell12520 ⟨58, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (3283484875947 / 4000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (2274410461101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12520_59 : CellCertificate 12520 (178357716519407 / 2000000000000000 : ℝ) (209709744328651 / 125000000000000000 : ℝ) (339001458598949 / 10000000000000000 : ℝ)
    (cell12520 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · norm_num [cell12520]
  · have h := gap_lower (n := 12520) (a := (41026742231419 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568603621113 / 25000000000000 : ℝ))
      (E := (cell12520 ⟨59, by decide⟩).energy) (xi := (339001458598949 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12520 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12520]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12520])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12520) (a := (41026742231419 / 50000000000000 : ℝ)) (b := (82275138739 / 50000000000000 : ℝ)) (q := (568603621113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12520])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12520]

theorem cert12521_40 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82696587593793 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274208500947 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨40, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82696587593793 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274208500947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_41 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (5166408032069 / 6250000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227421250991 / 10000000000000 : ℝ))
      (E := (cell12521 ⟨41, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (5166408032069 / 6250000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227421250991 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_42 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82628493120763 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71069264433 / 3125000000000 : ℝ))
      (E := (cell12521 ⟨42, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82628493120763 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (71069264433 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_43 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82594481386941 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227422047379 / 10000000000000 : ℝ))
      (E := (cell12521 ⟨43, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82594481386941 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (227422047379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_44 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41280246640979 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274224486211 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨44, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41280246640979 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274224486211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_45 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82526528776287 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284278562269 / 12500000000000 : ℝ))
      (E := (cell12521 ⟨45, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82526528776287 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (284278562269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_46 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20623146960137 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274232508431 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨46, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20623146960137 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274232508431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_47 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82458670445509 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274236515649 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨47, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82458670445509 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274236515649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_48 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (16484955312417 / 20000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274240518191 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨48, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (16484955312417 / 20000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274240518191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_49 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82390906161337 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274244514227 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨49, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82390906161337 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274244514227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_50 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82357059214473 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137124250857 / 50000000000000 : ℝ))
      (E := (cell12521 ⟨50, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82357059214473 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (1137124250857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_51 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20580808923211 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454850495679 / 20000000000000 : ℝ))
      (E := (cell12521 ⟨51, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20580808923211 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (454850495679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_52 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (10286179445993 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568564125203 / 25000000000000 : ℝ))
      (E := (cell12521 ⟨52, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (10286179445993 / 12500000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568564125203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_53 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82255658811411 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274260507321 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨53, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82255658811411 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274260507321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_54 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (41110952697513 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568566123757 / 25000000000000 : ℝ))
      (E := (cell12521 ⟨54, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (41110952697513 / 50000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568566123757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_55 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (8218817529071 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274268519913 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨55, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (8218817529071 / 10000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274268519913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_56 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82154468470523 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274272519631 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨56, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82154468470523 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274272519631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_57 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (20530196226667 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (113713824533 / 5000000000000 : ℝ))
      (E := (cell12521 ⟨57, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (20530196226667 / 25000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (113713824533 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_58 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82087124571483 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274280547581 / 100000000000000 : ℝ))
      (E := (cell12521 ⟨58, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82087124571483 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (2274280547581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12521_59 : CellCertificate 12521 (222939967779861 / 2500000000000000 : ℝ) (167754392081051 / 100000000000000000 : ℝ) (84743425210441 / 2500000000000000 : ℝ)
    (cell12521 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · norm_num [cell12521]
  · have h := gap_lower (n := 12521) (a := (82053487437447 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568571127267 / 25000000000000 : ℝ))
      (E := (cell12521 ⟨59, by decide⟩).energy) (xi := (84743425210441 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12521 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12521]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12521])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12521) (a := (82053487437447 / 100000000000000 : ℝ)) (b := (8226848487 / 5000000000000 : ℝ)) (q := (568571127267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12521])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12521]

theorem cert12522_40 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (20674146190861 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (227407857517 / 10000000000000 : ℝ))
      (E := (cell12522 ⟨40, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (20674146190861 / 25000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (227407857517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_41 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82662525992099 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274082568861 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨41, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82662525992099 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274082568861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_42 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (3305139636347 / 4000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (284260820627 / 12500000000000 : ℝ))
      (E := (cell12522 ⟨42, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (3305139636347 / 4000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (284260820627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_43 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82594479483341 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274090563109 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨43, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82594479483341 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274090563109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_44 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82560491686423 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568523640597 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨44, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82560491686423 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568523640597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_45 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (8252652748839 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274098561891 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨45, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (8252652748839 / 10000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274098561891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_46 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (16498517371973 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (142131410027 / 6250000000000 : ℝ))
      (E := (cell12522 ⟨46, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (16498517371973 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (142131410027 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_47 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (2576833430363 / 3125000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137053307753 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨47, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (2576833430363 / 3125000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137053307753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_48 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (32197178201 / 39062500000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274110607731 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨48, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (32197178201 / 39062500000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274110607731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_49 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82390906099757 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274114594151 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨49, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82390906099757 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274114594151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_50 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82357059458417 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137059286359 / 50000000000000 : ℝ))
      (E := (cell12522 ⟨50, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82357059458417 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (1137059286359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_51 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82323236241891 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568530650041 / 25000000000000 : ℝ))
      (E := (cell12522 ⟨51, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82323236241891 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (568530650041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_52 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41144718210837 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274126615079 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨52, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41144718210837 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274126615079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_53 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41127829984703 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274130614779 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨53, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41127829984703 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274130614779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_54 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41110953428433 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274134596373 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨54, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41110953428433 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274134596373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_55 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41094088527989 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (14213366349 / 625000000000 : ℝ))
      (E := (cell12522 ⟨55, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41094088527989 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (14213366349 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_56 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (41077235269401 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274142610833 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨56, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (41077235269401 / 50000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274142610833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_57 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82120787277541 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (14213416481 / 625000000000 : ℝ))
      (E := (cell12522 ⟨57, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82120787277541 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (14213416481 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_58 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (16417425448907 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274150631411 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨58, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (16417425448907 / 20000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274150631411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12522_59 : CellCertificate 12522 (445865582025569 / 5000000000000000 : ℝ) (1677409908406683 / 1000000000000000000 : ℝ) (338945947711227 / 10000000000000000 : ℝ)
    (cell12522 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · norm_num [cell12522]
  · have h := gap_lower (n := 12522) (a := (82053490412263 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274154590249 / 100000000000000 : ℝ))
      (E := (cell12522 ⟨59, by decide⟩).energy) (xi := (338945947711227 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12522 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12522]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12522])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12522) (a := (82053490412263 / 100000000000000 : ℝ)) (b := (6580946567 / 4000000000000 : ℝ)) (q := (2274154590249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12522])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12522]

theorem cert12523_40 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (1292134092719 / 1562500000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136974352391 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨40, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (1292134092719 / 1562500000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136974352391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_41 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82662523471977 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (17765255797 / 781250000000 : ℝ))
      (E := (cell12523 ⟨41, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82662523471977 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (17765255797 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_42 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (8262848869743 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (227395672369 / 10000000000000 : ℝ))
      (E := (cell12523 ⟨42, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (8262848869743 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (227395672369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_43 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82594477580549 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136980354001 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨43, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82594477580549 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136980354001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_44 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (10320061261457 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568491188257 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨44, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (10320061261457 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568491188257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_45 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (10315815775153 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136984370089 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨45, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (10315815775153 / 12500000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136984370089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_46 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (659940687039 / 800000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136986363533 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨46, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (659940687039 / 800000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1136986363533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_47 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82458669098379 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568494178073 / 25000000000000 : ℝ))
      (E := (cell12523 ⟨47, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82458669098379 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (568494178073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_48 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (20606193956913 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273980753159 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨48, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (20606193956913 / 25000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273980753159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_49 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82390906038757 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273984730023 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨49, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82390906038757 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273984730023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_50 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82357059702903 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273988758697 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨50, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82357059702903 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273988758697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_51 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82323236791443 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273992719017 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨51, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82323236791443 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273992719017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_52 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (2571544914871 / 3125000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273996726467 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨52, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (2571544914871 / 3125000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2273996726467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_53 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (8225566112783 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1137000359699 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨53, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (8225566112783 / 10000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1137000359699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_54 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82221908319099 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274004753977 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨54, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82221908319099 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274004753977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_55 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82188178821601 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274008768087 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨55, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82188178821601 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274008768087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_56 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82154472607399 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (142125797401 / 6250000000000 : ℝ))
      (E := (cell12523 ⟨56, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82154472607399 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (142125797401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_57 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (16424157929739 / 20000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274016780573 / 100000000000000 : ℝ))
      (E := (cell12523 ⟨57, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (16424157929739 / 20000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (2274016780573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_58 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (82087129917831 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454804154349 / 20000000000000 : ℝ))
      (E := (cell12523 ⟨58, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (82087129917831 / 100000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (454804154349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12523_59 : CellCertificate 12523 (891702461391051 / 10000000000000000 : ℝ) (838637958706297 / 500000000000000000 : ℝ) (16945909960303 / 500000000000000 : ℝ)
    (cell12523 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · norm_num [cell12523]
  · have h := gap_lower (n := 12523) (a := (41026746693643 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1137012393587 / 50000000000000 : ℝ))
      (E := (cell12523 ⟨59, by decide⟩).energy) (xi := (16945909960303 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12523 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12523]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12523])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12523) (a := (41026746693643 / 50000000000000 : ℝ)) (b := (164510360781 / 100000000000000 : ℝ)) (q := (1137012393587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12523])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12523]

theorem cert12524_40 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82696579105507 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136909444891 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨40, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82696579105507 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136909444891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_41 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (2583203779773 / 3125000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273822911869 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨41, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (2583203779773 / 3125000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273822911869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_42 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82628486487029 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273826937877 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨42, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82628486487029 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273826937877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_43 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41297237839281 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273830908471 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨43, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41297237839281 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273830908471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_44 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82560488497657 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136917470241 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨44, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82560488497657 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136917470241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_45 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82526524914787 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136919457659 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨45, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82526524914787 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136919457659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_46 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82492584900577 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273842949463 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨46, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82492584900577 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273842949463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_47 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (20614667106449 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136923461899 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨47, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (20614667106449 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136923461899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_48 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82424775461361 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454770179111 / 20000000000000 : ℝ))
      (E := (cell12524 ⟨48, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82424775461361 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (454770179111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_49 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82390905978337 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273854921843 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨49, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82390905978337 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273854921843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_50 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (20589264986983 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273858941721 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨50, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (20589264986983 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273858941721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_51 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82323237341499 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568465738233 / 25000000000000 : ℝ))
      (E := (cell12524 ⟨51, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82323237341499 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (568465738233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_52 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82289438130537 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136933476501 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨52, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82289438130537 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136933476501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_53 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (16451132457337 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142116933703 / 6250000000000 : ℝ))
      (E := (cell12524 ⟨53, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (16451132457337 / 20000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (142116933703 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_54 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (3288876391269 / 4000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136937454389 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨54, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (3288876391269 / 4000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136937454389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_55 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (4109409029379 / 5000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (227387891757 / 10000000000000 : ℝ))
      (E := (cell12524 ⟨55, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (4109409029379 / 5000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (227387891757 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_56 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (41077237338157 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273882962381 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨56, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (41077237338157 / 50000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273882962381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_57 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82120792020131 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136943460749 / 50000000000000 : ℝ))
      (E := (cell12524 ⟨57, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82120792020131 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (1136943460749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_58 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (82087132591371 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (284236371073 / 12500000000000 : ℝ))
      (E := (cell12524 ⟨58, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (82087132591371 / 100000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (284236371073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

theorem cert12524_59 : CellCertificate 12524 (891673763138121 / 10000000000000000 : ℝ) (1677141947823113 / 1000000000000000000 : ℝ) (338890455324987 / 10000000000000000 : ℝ)
    (cell12524 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · norm_num [cell12524]
  · have h := gap_lower (n := 12524) (a := (20513374090629 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273894981487 / 100000000000000 : ℝ))
      (E := (cell12524 ⟨59, by decide⟩).energy) (xi := (338890455324987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12524 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12524]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12524])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12524) (a := (20513374090629 / 25000000000000 : ℝ)) (b := (164497059559 / 100000000000000 : ℝ)) (q := (2273894981487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12524])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12524]

end BstLean.Part268
