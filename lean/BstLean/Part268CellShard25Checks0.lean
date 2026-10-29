import BstLean.Part268CellShard25Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12975_0 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (42035959080091 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218867506121 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨0, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (42035959080091 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218867506121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_1 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (84037028534009 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277358940187 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨1, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (84037028534009 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277358940187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_2 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (84002163721513 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218875474301 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨2, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (84002163721513 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218875474301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_3 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41983661843229 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109439744329 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨3, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41983661843229 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109439744329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_4 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (104915635491 / 125000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218883514827 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨4, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (104915635491 / 125000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218883514827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_5 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83897717804683 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109443751359 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨5, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83897717804683 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109443751359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_6 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41931475943219 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (44377830357 / 2000000000000 : ℝ))
      (E := (cell12975 ⟨6, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41931475943219 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (44377830357 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_7 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41914105301293 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218895509579 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨7, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41914105301293 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218895509579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_8 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83793493917829 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554724885741 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨8, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83793493917829 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554724885741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_9 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83758801797059 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109451754381 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨9, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83758801797059 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109451754381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_10 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (16744826841069 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218907529583 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨10, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (16744826841069 / 20000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218907529583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_11 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (10461186388493 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554727888421 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨11, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (10461186388493 / 12500000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554727888421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_12 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (5228429529393 / 6250000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554728882247 / 25000000000000 : ℝ))
      (E := (cell12975 ⟨12, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (5228429529393 / 6250000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (554728882247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_13 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41810139128997 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443783903871 / 20000000000000 : ℝ))
      (E := (cell12975 ⟨13, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41810139128997 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (443783903871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_14 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41792854218427 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218923530333 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨14, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41792854218427 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218923530333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_15 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83551162972837 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218927567223 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨15, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83551162972837 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218927567223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_16 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (20879160458023 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218931576871 / 100000000000000 : ℝ))
      (E := (cell12975 ⟨16, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (20879160458023 / 25000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (2218931576871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_17 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (41741072490469 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109467782013 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨17, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (41741072490469 / 50000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109467782013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_18 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83447672385873 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277367448931 / 12500000000000 : ℝ))
      (E := (cell12975 ⟨18, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83447672385873 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (277367448931 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12975_19 : CellCertificate 12975 (879164267605591 / 10000000000000000 : ℝ) (1618827154694463 / 1000000000000000000 : ℝ) (326830634096151 / 10000000000000000 : ℝ)
    (cell12975 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · norm_num [cell12975]
  · have h := gap_lower (n := 12975) (a := (83413224013563 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109471802597 / 50000000000000 : ℝ))
      (E := (cell12975 ⟨19, by decide⟩).energy) (xi := (326830634096151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12975 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12975]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12975])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12975) (a := (83413224013563 / 100000000000000 : ℝ)) (b := (79355621871 / 50000000000000 : ℝ)) (q := (1109471802597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12975])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12975]

theorem cert12976_0 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (84071903667349 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (17750021373 / 800000000000 : ℝ))
      (E := (cell12976 ⟨0, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (84071903667349 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (17750021373 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_1 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (8403701404761 / 10000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218756681221 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨1, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (8403701404761 / 10000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218756681221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_2 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (42001074620771 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218760686179 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨2, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (42001074620771 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218760686179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_3 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (8396730921291 / 10000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218764636967 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨3, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (8396730921291 / 10000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218764636967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_4 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83932493925669 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109384328749 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨4, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83932493925669 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109384328749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_5 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41948851671981 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109386348877 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨5, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41948851671981 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109386348877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_6 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83862937432123 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554694162347 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨6, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83862937432123 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554694162347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_7 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83828196154669 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109390346811 / 50000000000000 : ℝ))
      (E := (cell12976 ⟨7, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83828196154669 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109390346811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_8 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83793479476307 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554696165889 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨8, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83793479476307 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554696165889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_9 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20939696840481 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109394341 / 50000000000 : ℝ))
      (E := (cell12976 ⟨9, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20939696840481 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (1109394341 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_10 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83724119776593 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (138674543593 / 6250000000000 : ℝ))
      (E := (cell12976 ⟨10, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83724119776593 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (138674543593 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_11 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (326912018303 / 390625000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218796716303 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨11, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (326912018303 / 390625000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218796716303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_12 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (20913714513571 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69337521449 / 3125000000000 : ℝ))
      (E := (cell12976 ⟨12, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (20913714513571 / 25000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (69337521449 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_13 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16724052769671 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554701182421 / 25000000000000 : ℝ))
      (E := (cell12976 ⟨13, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16724052769671 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (554701182421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_14 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41792847016787 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (110940436777 / 5000000000000 : ℝ))
      (E := (cell12976 ⟨14, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41792847016787 / 50000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (110940436777 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_15 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (10443893571989 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218812709167 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨15, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (10443893571989 / 12500000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218812709167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_16 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16703325488303 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218816713763 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨16, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16703325488303 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218816713763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_17 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (16696426119341 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218820754147 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨17, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (16696426119341 / 20000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218820754147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_18 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (83447658007977 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (277353089797 / 12500000000000 : ℝ))
      (E := (cell12976 ⟨18, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (83447658007977 / 100000000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (277353089797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12976_19 : CellCertificate 12976 (879137457625147 / 10000000000000000 : ℝ) (323740471812937 / 200000000000000000 : ℝ) (2614438866631 / 80000000000000 : ℝ)
    (cell12976 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · norm_num [cell12976]
  · have h := gap_lower (n := 12976) (a := (41706604821 / 50000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218828727209 / 100000000000000 : ℝ))
      (E := (cell12976 ⟨19, by decide⟩).energy) (xi := (2614438866631 / 80000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12976 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12976]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12976])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12976) (a := (41706604821 / 50000000000 : ℝ)) (b := (79349434863 / 50000000000000 : ℝ)) (q := (2218828727209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12976])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12976]

theorem cert12977_0 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (84071889176753 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (27732972909 / 1250000000000 : ℝ))
      (E := (cell12977 ⟨0, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (84071889176753 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (27732972909 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_1 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (84036999563447 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218641836539 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨1, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (84036999563447 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218641836539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_2 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (84002134763807 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443729167153 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨2, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (84002134763807 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443729167153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_3 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (20991823685399 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109324919389 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨3, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (20991823685399 / 25000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109324919389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_4 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (8393247946077 / 10000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218653853697 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨4, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (8393247946077 / 10000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218653853697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_5 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83897688885473 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (69333057201 / 3125000000000 : ℝ))
      (E := (cell12977 ⟨5, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83897688885473 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (69333057201 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_6 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41931461490019 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109330917251 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨6, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41931461490019 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109330917251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_7 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83828181708983 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218665873263 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨7, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83828181708983 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218665873263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_8 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83793465037013 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554667473949 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨8, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83793465037013 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554667473949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_9 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83758772929017 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109336925419 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨9, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83758772929017 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109336925419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_10 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83724105350067 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109338930497 / 50000000000000 : ℝ))
      (E := (cell12977 ⟨10, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83724105350067 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (1109338930497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_11 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41844731132709 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88747274981 / 4000000000000 : ℝ))
      (E := (cell12977 ⟨11, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41844731132709 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (88747274981 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_12 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (10456855455063 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218685897469 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨12, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (10456855455063 / 12500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218685897469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_13 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83620249440939 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218689877477 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨13, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83620249440939 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218689877477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_14 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83585679632517 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554673469547 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨14, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83585679632517 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554673469547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_15 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83551134181209 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277337238113 / 12500000000000 : ℝ))
      (E := (cell12977 ⟨15, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83551134181209 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (277337238113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_16 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (2087915326329 / 2500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218701904473 / 100000000000000 : ℝ))
      (E := (cell12977 ⟨16, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (2087915326329 / 2500000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (2218701904473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_17 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (83482116214691 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554676484969 / 25000000000000 : ℝ))
      (E := (cell12977 ⟨17, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (83482116214691 / 100000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (554676484969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_18 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (834476436323 / 1000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221870989917 / 10000000000000 : ℝ))
      (E := (cell12977 ⟨18, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (834476436323 / 1000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (221870989917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12977_19 : CellCertificate 12977 (879110651603621 / 10000000000000000 : ℝ) (32371551653489 / 20000000000000000 : ℝ) (326779086663553 / 10000000000000000 : ℝ)
    (cell12977 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · norm_num [cell12977]
  · have h := gap_lower (n := 12977) (a := (41706597636327 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443742780623 / 20000000000000 : ℝ))
      (E := (cell12977 ⟨19, by decide⟩).energy) (xi := (326779086663553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12977 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12977]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12977])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12977) (a := (41706597636327 / 50000000000000 : ℝ)) (b := (158686497649 / 100000000000000 : ℝ)) (q := (443742780623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12977])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12977]

theorem cert12978_0 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (84071874688393 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109261523623 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨0, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (84071874688393 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109261523623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_1 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (84036985081519 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (34664485083 / 1562500000000 : ℝ))
      (E := (cell12978 ⟨1, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (84036985081519 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (34664485083 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_2 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16800424057661 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218531038833 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨2, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16800424057661 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218531038833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_3 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41983640136257 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218535036187 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨3, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41983640136257 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218535036187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_4 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83932464998103 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218539045493 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨4, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83932464998103 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218539045493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_5 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (16779534885843 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109271537309 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨5, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (16779534885843 / 20000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109271537309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_6 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41931454265091 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218547073193 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨6, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41931454265091 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218547073193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_7 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (3353126690621 / 4000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443710209701 / 20000000000000 : ℝ))
      (E := (cell12978 ⟨7, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (3353126690621 / 4000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443710209701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_8 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83793450599947 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109277532807 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨8, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83793450599947 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109277532807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_9 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83758758498337 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109279536663 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨9, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83758758498337 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109279536663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_10 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83724090925767 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (88742523127 / 4000000000000 : ℝ))
      (E := (cell12978 ⟨10, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83724090925767 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (88742523127 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_11 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83689447847493 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443713417289 / 20000000000000 : ℝ))
      (E := (cell12978 ⟨11, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83689447847493 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443713417289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_12 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (20913707307237 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (88742844167 / 4000000000000 : ℝ))
      (E := (cell12978 ⟨12, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (20913707307237 / 25000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (88742844167 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_13 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83620235035747 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277321884877 / 12500000000000 : ℝ))
      (E := (cell12978 ⟨13, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83620235035747 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (277321884877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_14 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83585665233683 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218579132771 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨14, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83585665233683 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218579132771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_15 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (41775559894363 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1774866477 / 80000000000 : ℝ))
      (E := (cell12978 ⟨15, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (41775559894363 / 50000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1774866477 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_16 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (5219787416689 / 6250000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218587090791 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨16, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (5219787416689 / 6250000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218587090791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_17 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83482101834897 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109295560607 / 50000000000000 : ℝ))
      (E := (cell12978 ⟨17, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83482101834897 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (1109295560607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_18 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (83447629258841 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218595133833 / 100000000000000 : ℝ))
      (E := (cell12978 ⟨18, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (83447629258841 / 100000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (2218595133833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12978_19 : CellCertificate 12978 (175816769908019 / 2000000000000000 : ℝ) (161845282551931 / 100000000000000000 : ℝ) (326753319099143 / 10000000000000000 : ℝ)
    (cell12978 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · norm_num [cell12978]
  · have h := gap_lower (n := 12978) (a := (3336527236221 / 4000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443719826583 / 20000000000000 : ℝ))
      (E := (cell12978 ⟨19, by decide⟩).energy) (xi := (326753319099143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12978 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12978]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12978])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12978) (a := (3336527236221 / 4000000000000 : ℝ)) (b := (15867412751 / 10000000000000 : ℝ)) (q := (443719826583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12978])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12978]

theorem cert12979_0 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (21017965050567 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277301032171 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨0, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (21017965050567 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277301032171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_1 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (3361478824073 / 4000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109206124841 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨1, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (3361478824073 / 4000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109206124841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_2 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (21000526453759 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109208147691 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨2, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (21000526453759 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109208147691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_3 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16793453161133 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218420287101 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨3, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16793453161133 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218420287101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_4 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83932450537667 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (110921214541 / 5000000000000 : ℝ))
      (E := (cell12979 ⟨4, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83932450537667 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (110921214541 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_5 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83897659975187 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554607078601 / 25000000000000 : ℝ))
      (E := (cell12979 ⟨5, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83897659975187 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554607078601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_6 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83862894082557 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554608076871 / 25000000000000 : ℝ))
      (E := (cell12979 ⟨6, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83862894082557 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (554608076871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_7 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (10478519103037 / 12500000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218436277349 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨7, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (10478519103037 / 12500000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218436277349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_8 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20948359041277 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218440289059 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨8, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20948359041277 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218440289059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_9 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83758744069883 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218444291417 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨9, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83758744069883 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218444291417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_10 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83724076503693 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (27730603637 / 1250000000000 : ℝ))
      (E := (cell12979 ⟨10, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83724076503693 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (27730603637 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_11 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (5230589589487 / 6250000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218452293971 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨11, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (5230589589487 / 6250000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218452293971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_12 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16730962963923 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277307038311 / 12500000000000 : ℝ))
      (E := (cell12979 ⟨12, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16730962963923 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (277307038311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_13 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83620220632777 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218460334303 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨13, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83620220632777 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218460334303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_14 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (8358565083707 / 10000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109232162399 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨14, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (8358565083707 / 10000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109232162399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_15 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (16710221079693 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (138654271337 / 6250000000000 : ℝ))
      (E := (cell12979 ⟨15, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (16710221079693 / 20000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (138654271337 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_16 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (20879146070777 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218472330931 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨16, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (20879146070777 / 25000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218472330931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_17 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83482087457321 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109238178199 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨17, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83482087457321 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109238178199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_18 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (83447614887601 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218480364107 / 100000000000000 : ℝ))
      (E := (cell12979 ⟨18, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (83447614887601 / 100000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (2218480364107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12979_19 : CellCertificate 12979 (17581141028673 / 200000000000000 : ℝ) (25286376368669 / 15625000000000000 : ℝ) (81681888908651 / 2500000000000000 : ℝ)
    (cell12979 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · norm_num [cell12979]
  · have h := gap_lower (n := 12979) (a := (41706583270307 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109242179163 / 50000000000000 : ℝ))
      (E := (cell12979 ⟨19, by decide⟩).energy) (xi := (81681888908651 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12979 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12979]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12979])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12979) (a := (41706583270307 / 50000000000000 : ℝ)) (b := (39665439827 / 25000000000000 : ℝ)) (q := (1109242179163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12979])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12979]

theorem cert12980_0 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (42035922859189 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554573380231 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨0, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (42035922859189 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554573380231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_1 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (16807391224873 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221829750751 / 10000000000000 : ℝ))
      (E := (cell12980 ⟨1, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (16807391224873 / 20000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221829750751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_2 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (5250130709 / 6250000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218301547529 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨2, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (5250130709 / 6250000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218301547529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_3 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (10495906417631 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109152766807 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨3, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (10495906417631 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109152766807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_4 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83932436079463 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443661906349 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨4, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83932436079463 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443661906349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_5 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83897645523389 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221831354979 / 10000000000000 : ℝ))
      (E := (cell12980 ⟨5, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83897645523389 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (221831354979 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_6 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (2096571990929 / 2500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109158768689 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨6, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (2096571990929 / 2500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109158768689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_7 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41914069192647 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218321559799 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨7, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41914069192647 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218321559799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_8 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (5237088858281 / 6250000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554581391533 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨8, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (5237088858281 / 6250000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554581391533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_9 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (10469841205457 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218329563161 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨9, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (10469841205457 / 12500000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218329563161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_10 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20931015520961 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218333557421 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨10, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20931015520961 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218333557421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_11 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20922354754579 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554584388799 / 25000000000000 : ℝ))
      (E := (cell12980 ⟨11, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20922354754579 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (554584388799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_12 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41827400206253 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109170781263 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨12, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41827400206253 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109170781263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_13 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83620206232029 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218345585199 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨13, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83620206232029 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218345585199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_14 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41792818221339 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218349570599 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨14, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41792818221339 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218349570599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_15 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83551091010423 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443670716429 / 20000000000000 : ℝ))
      (E := (cell12980 ⟨15, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83551091010423 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (443670716429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_16 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83516569901411 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109178812447 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨16, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83516569901411 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109178812447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_17 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (20870518270491 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218361587193 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨17, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (20870518270491 / 25000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218361587193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_18 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (83447600518577 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109182794997 / 50000000000000 : ℝ))
      (E := (cell12980 ⟨18, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (83447600518577 / 100000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (1109182794997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12980_19 : CellCertificate 12980 (439515128641683 / 5000000000000000 : ℝ) (1618203368896523 / 1000000000000000000 : ℝ) (81675449067223 / 2500000000000000 : ℝ)
    (cell12980 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · norm_num [cell12980]
  · have h := gap_lower (n := 12980) (a := (41706576088959 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218369637633 / 100000000000000 : ℝ))
      (E := (cell12980 ⟨19, by decide⟩).energy) (xi := (81675449067223 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12980 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12980]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12980])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12980) (a := (41706576088959 / 50000000000000 : ℝ)) (b := (158649393043 / 100000000000000 : ℝ)) (q := (2218369637633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12980])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12980]

theorem cert12981_0 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (84071831236723 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554544695019 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨0, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (84071831236723 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554544695019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_1 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (84036941649139 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554545704699 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨1, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (84036941649139 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554545704699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_2 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (84002076875197 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109093397637 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨2, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (84002076875197 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109093397637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_3 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41983618439331 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109095416817 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨3, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41983618439331 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109095416817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_4 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (1311444087867 / 1562500000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554548706551 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨4, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (1311444087867 / 1562500000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554548706551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_5 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83897631073821 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554549709683 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨5, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83897631073821 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554549709683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_6 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (10482858149249 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218202820851 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨6, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (10482858149249 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218202820851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_7 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (2095703098713 / 2500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (44364136757 / 2000000000000 : ℝ))
      (E := (cell12981 ⟨7, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (2095703098713 / 2500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (44364136757 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_8 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83793407302111 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277276354851 / 12500000000000 : ℝ))
      (E := (cell12981 ⟨8, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83793407302111 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277276354851 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_9 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83758715219653 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (221821483051 / 10000000000000 : ℝ))
      (E := (cell12981 ⟨9, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83758715219653 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (221821483051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_10 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83724047666219 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (55455471939 / 2500000000000 : ℝ))
      (E := (cell12981 ⟨10, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83724047666219 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (55455471939 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_11 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83689404607063 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554555717531 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨11, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83689404607063 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554555717531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_12 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83654786007619 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218226872289 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨12, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83654786007619 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218226872289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_13 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41810095916751 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109115444923 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨13, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41810095916751 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109115444923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_14 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41792811025253 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (88729394807 / 4000000000000 : ℝ))
      (E := (cell12981 ⟨14, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41792811025253 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (88729394807 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_15 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83551076624601 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277279859587 / 12500000000000 : ℝ))
      (E := (cell12981 ⟨15, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83551076624601 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (277279859587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_16 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (83516555521933 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (34660044629 / 1562500000000 : ℝ))
      (E := (cell12981 ⟨16, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (83516555521933 / 100000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (34660044629 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_17 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (10435257338603 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554561717959 / 25000000000000 : ℝ))
      (E := (cell12981 ⟨17, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (10435257338603 / 12500000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (554561717959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_18 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (8344758615177 / 10000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218250869753 / 100000000000000 : ℝ))
      (E := (cell12981 ⟨18, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (8344758615177 / 10000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (2218250869753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12981_19 : CellCertificate 12981 (219750866772081 / 2500000000000000 : ℝ) (809039334709993 / 500000000000000000 : ℝ) (326676041000967 / 10000000000000000 : ℝ)
    (cell12981 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · norm_num [cell12981]
  · have h := gap_lower (n := 12981) (a := (41706568908719 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109127456277 / 50000000000000 : ℝ))
      (E := (cell12981 ⟨19, by decide⟩).energy) (xi := (326676041000967 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12981 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12981]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12981])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12981) (a := (41706568908719 / 50000000000000 : ℝ)) (b := (31727405743 / 20000000000000 : ℝ)) (q := (1109127456277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12981])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12981]

theorem cert12982_0 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (84071816757301 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443612818533 / 20000000000000 : ℝ))
      (E := (cell12982 ⟨0, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (84071816757301 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443612818533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_1 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (16807385435229 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109034062841 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨1, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (16807385435229 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109034062841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_2 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (42001031204313 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277259012063 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨2, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (42001031204313 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277259012063 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_3 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83967222418507 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277259516157 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨3, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83967222418507 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277259516157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_4 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (5245775448109 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218080116263 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨4, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (5245775448109 / 6250000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218080116263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_5 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83897616626481 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218084123277 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨5, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83897616626481 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218084123277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_6 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (20965712688263 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109044078953 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨6, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (20965712688263 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109044078953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_7 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41914054756987 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218092169507 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨7, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41914054756987 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218092169507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_8 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (2618543527311 / 3125000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443619233023 / 20000000000000 : ℝ))
      (E := (cell12982 ⟨8, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (2618543527311 / 3125000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443619233023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_9 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (20939675199469 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218100151513 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨9, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (20939675199469 / 25000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218100151513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_10 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41862016625409 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443620827047 / 20000000000000 : ℝ))
      (E := (cell12982 ⟨10, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41862016625409 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (443620827047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_11 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83689390198033 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (110905409033 / 5000000000000 : ℝ))
      (E := (cell12982 ⟨11, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83689390198033 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (110905409033 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_12 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41827385802477 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109056088831 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨12, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41827385802477 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109056088831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_13 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83620177437197 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109058095051 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨13, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83620177437197 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109058095051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_14 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (16717121532111 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218120165361 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨14, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (16717121532111 / 20000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218120165361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_15 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41775531120499 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218124166859 / 100000000000000 : ℝ))
      (E := (cell12982 ⟨15, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41775531120499 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (2218124166859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_16 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83516541144673 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109064099827 / 50000000000000 : ℝ))
      (E := (cell12982 ⟨16, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83516541144673 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (1109064099827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_17 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83482044337901 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277266526291 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨17, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83482044337901 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277266526291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_18 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (83447571787179 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277267025423 / 12500000000000 : ℝ))
      (E := (cell12982 ⟨18, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (83447571787179 / 100000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (277267025423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12982_19 : CellCertificate 12982 (878976680847607 / 10000000000000000 : ℝ) (1617953989160761 / 1000000000000000000 : ℝ) (326650289829787 / 10000000000000000 : ℝ)
    (cell12982 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · norm_num [cell12982]
  · have h := gap_lower (n := 12982) (a := (41706561729587 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (221814018309 / 10000000000000 : ℝ))
      (E := (cell12982 ⟨19, by decide⟩).energy) (xi := (326650289829787 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12982 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12982]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12982])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12982) (a := (41706561729587 / 50000000000000 : ℝ)) (b := (158624666323 / 100000000000000 : ℝ)) (q := (221814018309 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12982])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12982]

theorem cert12983_0 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (84071802280113 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554487364673 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨0, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (84071802280113 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554487364673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_1 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10504614088173 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217953428169 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨1, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10504614088173 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217953428169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_2 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (42001023972143 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217957451221 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨2, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (42001023972143 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217957451221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_3 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41983603980291 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554490369597 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨3, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41983603980291 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554490369597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_4 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83932392718229 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108982729929 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨4, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83932392718229 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108982729929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_5 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (8389760218137 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108984730691 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨5, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (8389760218137 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108984730691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_6 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83862836314339 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217973490567 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨6, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83862836314339 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217973490567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_7 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83828095081653 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554494374193 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨7, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83828095081653 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554494374193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_8 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (41896689224009 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221798148703 / 10000000000000 : ℝ))
      (E := (cell12983 ⟨8, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (41896689224009 / 50000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221798148703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_9 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (20939671594581 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554496367031 / 25000000000000 : ℝ))
      (E := (cell12983 ⟨9, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (20939671594581 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (554496367031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_10 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83724018837641 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108994752331 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨10, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83724018837641 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108994752331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_11 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (3347575031649 / 4000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217993486807 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨11, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (3347575031649 / 4000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2217993486807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_12 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83654757204511 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108998739323 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨12, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83654757204511 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1108998739323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_13 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (10452520380389 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221800148597 / 10000000000000 : ℝ))
      (E := (cell12983 ⟨13, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (10452520380389 / 12500000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (221800148597 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_14 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83585593272823 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (88720220573 / 4000000000000 : ℝ))
      (E := (cell12983 ⟨14, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83585593272823 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (88720220573 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_15 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83551047859613 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (277251188853 / 12500000000000 : ℝ))
      (E := (cell12983 ⟨15, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83551047859613 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (277251188853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_16 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (8351652676963 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218013538667 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨16, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (8351652676963 / 10000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218013538667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_17 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (16696405993839 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443603508887 / 20000000000000 : ℝ))
      (E := (cell12983 ⟨17, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (16696405993839 / 20000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (443603508887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_18 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (83447557424803 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218021532633 / 100000000000000 : ℝ))
      (E := (cell12983 ⟨18, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (83447557424803 / 100000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (2218021532633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12983_19 : CellCertificate 12983 (175789979712059 / 2000000000000000 : ℝ) (808914664057203 / 500000000000000000 : ℝ) (326624542754313 / 10000000000000000 : ℝ)
    (cell12983 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · norm_num [cell12983]
  · have h := gap_lower (n := 12983) (a := (20853277275781 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109012753763 / 50000000000000 : ℝ))
      (E := (cell12983 ⟨19, by decide⟩).energy) (xi := (326624542754313 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12983 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12983]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12983])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12983) (a := (20853277275781 / 25000000000000 : ℝ)) (b := (79306152933 / 50000000000000 : ℝ)) (q := (1109012753763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12983])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12983]

theorem cert12984_0 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (42035893902579 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27722934531 / 1250000000000 : ℝ))
      (E := (cell12984 ⟨0, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (42035893902579 / 50000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27722934531 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_1 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16807379647371 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108919392059 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨1, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16807379647371 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108919392059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_2 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (84002033482177 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (110892140077 / 5000000000000 : ℝ))
      (E := (cell12984 ⟨2, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (84002033482177 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (110892140077 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_3 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (10495899188111 / 12500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217846823123 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨3, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (10495899188111 / 12500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217846823123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_4 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83932378268943 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217850799057 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨4, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83932378268943 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217850799057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_5 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83897587738487 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217854795091 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨5, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83897587738487 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217854795091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_6 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83862821877853 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108929409417 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨6, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83862821877853 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108929409417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_7 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83828080651559 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217862819643 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨7, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83828080651559 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217862819643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_8 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (8379336402431 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277233350569 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨8, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (8379336402431 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277233350569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_9 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16751734392199 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217870838393 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨9, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16751734392199 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217870838393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_10 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83724004426687 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217874811627 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨10, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83724004426687 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217874811627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_11 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (1046117017333 / 1250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217878846659 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨11, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (1046117017333 / 1250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217878846659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_12 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (5228421425393 / 6250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27723535417 / 1250000000000 : ℝ))
      (E := (cell12984 ⟨12, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (5228421425393 / 6250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (27723535417 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_13 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (5226259290703 / 6250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277235854449 / 12500000000000 : ℝ))
      (E := (cell12984 ⟨13, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (5226259290703 / 6250000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (277235854449 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_14 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (8358557888731 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217890858903 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨14, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (8358557888731 / 10000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217890858903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_15 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83551033480447 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217894850403 / 100000000000000 : ℝ))
      (E := (cell12984 ⟨15, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83551033480447 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (2217894850403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_16 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16703302479361 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443579774659 / 20000000000000 : ℝ))
      (E := (cell12984 ⟨16, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16703302479361 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (443579774659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_17 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (16696403120541 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108951437079 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨17, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (16696403120541 / 20000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108951437079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_18 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (83447543064643 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108953428749 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨18, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (83447543064643 / 100000000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108953428749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12984_19 : CellCertificate 12984 (878923120225473 / 10000000000000000 : ℝ) (1617704686276481 / 1000000000000000000 : ℝ) (5103106246461 / 156250000000000 : ℝ)
    (cell12984 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · norm_num [cell12984]
  · have h := gap_lower (n := 12984) (a := (10426636843661 / 12500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108955442931 / 50000000000000 : ℝ))
      (E := (cell12984 ⟨19, by decide⟩).energy) (xi := (5103106246461 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12984 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12984]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12984])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12984) (a := (10426636843661 / 12500000000000 : ℝ)) (b := (9912496709 / 6250000000000 : ℝ)) (q := (1108955442931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12984])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12984]

theorem cert12985_0 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (16814354666487 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217720177547 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨0, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (16814354666487 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217720177547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_1 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (84036883770557 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217724193531 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨1, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (84036883770557 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217724193531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_2 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (42001009511149 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108864073731 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨2, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (42001009511149 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108864073731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_3 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41983589525711 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217732163463 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨3, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41983589525711 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217732163463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_4 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (16786472764377 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217736191793 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨4, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (16786472764377 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217736191793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_5 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (10487196662229 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (55443504559 / 2500000000000 : ℝ))
      (E := (cell12985 ⟨5, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (10487196662229 / 12500000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (55443504559 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_6 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83862807443593 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108872100343 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨6, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83862807443593 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108872100343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_7 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83828066223689 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554437049031 / 25000000000000 : ℝ))
      (E := (cell12985 ⟨7, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83828066223689 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554437049031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_8 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (3351733984113 / 4000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554438043927 / 25000000000000 : ℝ))
      (E := (cell12985 ⟨8, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (3351733984113 / 4000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (554438043927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_9 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (8375865754589 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217756204271 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨9, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (8375865754589 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217756204271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_10 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (16744798003591 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108880115173 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨10, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (16744798003591 / 20000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108880115173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_11 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20922336746069 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108882101061 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨11, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20922336746069 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108882101061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_12 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (83654728410287 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217768241803 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨12, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (83654728410287 / 100000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217768241803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_13 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41810067130801 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221777223897 / 10000000000000 : ℝ))
      (E := (cell12985 ⟨13, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41810067130801 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (221777223897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_14 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (5224097781501 / 6250000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217776257259 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨14, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (5224097781501 / 6250000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217776257259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_15 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41775509551749 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217780243787 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨15, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41775509551749 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217780243787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_16 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (20879124506549 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217784261751 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨16, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (20879124506549 / 25000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217784261751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_17 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (8348200123843 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108894128867 / 50000000000000 : ℝ))
      (E := (cell12985 ⟨17, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (8348200123843 / 10000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (1108894128867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_18 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41723764353349 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217792236239 / 100000000000000 : ℝ))
      (E := (cell12985 ⟨18, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41723764353349 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (2217792236239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12985_19 : CellCertificate 12985 (878896345842221 / 10000000000000000 : ℝ) (1617580063642547 / 1000000000000000000 : ℝ) (326573060886321 / 10000000000000000 : ℝ)
    (cell12985 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · norm_num [cell12985]
  · have h := gap_lower (n := 12985) (a := (41706540198833 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277224532477 / 12500000000000 : ℝ))
      (E := (cell12985 ⟨19, by decide⟩).energy) (xi := (326573060886321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12985 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12985]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12985])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12985) (a := (41706540198833 / 50000000000000 : ℝ)) (b := (158587590757 / 100000000000000 : ℝ)) (q := (277224532477 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12985])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12985]

theorem cert12986_0 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (10508969857743 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277200698527 / 12500000000000 : ℝ))
      (E := (cell12986 ⟨0, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (10508969857743 / 12500000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (277200698527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_1 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (8403686930649 / 10000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108804770343 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨1, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (8403686930649 / 10000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108804770343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_2 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (84002004564649 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217613546873 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨2, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (84002004564649 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217613546873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_3 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41983582300093 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554404389329 / 25000000000000 : ℝ))
      (E := (cell12986 ⟨3, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41983582300093 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (554404389329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_4 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (2622885918033 / 3125000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108810790067 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨4, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (2622885918033 / 3125000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108810790067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_5 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83897558859403 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108812782619 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨5, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83897558859403 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108812782619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_6 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83862793011559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108814789073 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨6, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83862793011559 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108814789073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_7 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16765610359609 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217633568213 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨7, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16765610359609 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217633568213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_8 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16758667036713 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108818800249 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨8, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16758667036713 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108818800249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_9 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83758643133007 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217641623809 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨9, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83758643133007 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217641623809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_10 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16744795122289 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443529117321 / 20000000000000 : ℝ))
      (E := (cell12986 ⟨10, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16744795122289 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443529117321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_11 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83689332584133 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217649611293 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨11, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83689332584133 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217649611293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_12 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (16730942803301 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108826822931 / 50000000000000 : ℝ))
      (E := (cell12986 ⟨12, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (16730942803301 / 20000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (1108826822931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_13 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (653282186517 / 781250000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217657637961 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨13, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (653282186517 / 781250000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217657637961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_14 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (4179277506147 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217661651231 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨14, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (4179277506147 / 5000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217661651231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_15 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83551004728767 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443533126557 / 20000000000000 : ℝ))
      (E := (cell12986 ⟨15, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83551004728767 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (443533126557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_16 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83516483657803 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (4331386027 / 195312500000 : ℝ))
      (E := (cell12986 ⟨16, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83516483657803 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (4331386027 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_17 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83481986876371 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217673636927 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨17, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83481986876371 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217673636927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_18 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (41723757175483 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217677668859 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨18, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (41723757175483 / 50000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217677668859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12986_19 : CellCertificate 12986 (439434787704811 / 5000000000000000 : ℝ) (808727730104083 / 500000000000000000 : ℝ) (326547326091723 / 10000000000000000 : ℝ)
    (cell12986 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · norm_num [cell12986]
  · have h := gap_lower (n := 12986) (a := (83413066048257 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217681687673 / 100000000000000 : ℝ))
      (E := (cell12986 ⟨19, by decide⟩).energy) (xi := (326547326091723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12986 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12986]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12986])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12986) (a := (83413066048257 / 100000000000000 : ℝ)) (b := (19821904513 / 12500000000000 : ℝ)) (q := (2217681687673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12986])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12986]

theorem cert12987_0 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (21017936098421 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217490994489 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨0, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (21017936098421 / 25000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217490994489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_1 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (84036854844653 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217494999169 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨1, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (84036854844653 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217494999169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_2 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (84001990109229 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88699959991 / 4000000000000 : ℝ))
      (E := (cell12987 ⟨2, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (84001990109229 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88699959991 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_3 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41983575075589 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217503004683 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨3, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41983575075589 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217503004683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_4 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83932334934453 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443501404403 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨4, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83932334934453 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443501404403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_5 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (104871930529 / 125000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108755500839 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨5, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (104871930529 / 125000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108755500839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_6 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83862778581751 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217515009193 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨6, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83862778581751 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217515009193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_7 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (670624298997 / 800000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108759496957 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨7, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (670624298997 / 800000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108759496957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_8 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (1309270636977 / 1562500000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (22175230209 / 1000000000000 : ℝ))
      (E := (cell12987 ⟨8, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (1309270636977 / 1562500000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (22175230209 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_9 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83758628722347 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108763519479 / 50000000000000 : ℝ))
      (E := (cell12987 ⟨9, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83758628722347 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (1108763519479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_10 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83723961207157 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110876552731 / 5000000000000 : ℝ))
      (E := (cell12987 ⟨10, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83723961207157 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110876552731 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_11 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (8368931818621 / 10000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217535016077 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨11, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (8368931818621 / 10000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217535016077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_12 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41827349812471 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443507809107 / 20000000000000 : ℝ))
      (E := (cell12987 ⟨12, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41827349812471 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (443507809107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_13 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10452513186121 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277192879071 / 12500000000000 : ℝ))
      (E := (cell12987 ⟨13, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10452513186121 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (277192879071 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_14 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83585535744081 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110877352041 / 5000000000000 : ℝ))
      (E := (cell12987 ⟨14, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83585535744081 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (110877352041 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_15 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (83550990356251 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217551075591 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨15, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (83550990356251 / 100000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217551075591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_16 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41758234645813 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217555083727 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨16, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41758234645813 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217555083727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_17 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (41740986258263 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88702362799 / 4000000000000 : ℝ))
      (E := (cell12987 ⟨17, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (41740986258263 / 50000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (88702362799 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_18 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (10430937499681 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217563097099 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨18, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (10430937499681 / 12500000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217563097099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12987_19 : CellCertificate 12987 (21971070223169 / 250000000000000 : ℝ) (1617330875968901 / 1000000000000000000 : ℝ) (163260797694337 / 5000000000000000 : ℝ)
    (cell12987 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · norm_num [cell12987]
  · have h := gap_lower (n := 12987) (a := (4170652585053 / 5000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217567111151 / 100000000000000 : ℝ))
      (E := (cell12987 ⟨19, by decide⟩).energy) (xi := (163260797694337 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12987 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12987]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12987])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12987) (a := (4170652585053 / 5000000000000 : ℝ)) (b := (31712576677 / 20000000000000 : ℝ)) (q := (2217567111151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12987])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12987]

theorem cert12988_0 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (42035864963827 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443475290841 / 20000000000000 : ℝ))
      (E := (cell12988 ⟨0, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (42035864963827 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443475290841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_1 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (42018420192523 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108690226629 / 50000000000000 : ℝ))
      (E := (cell12988 ⟨1, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (42018420192523 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108690226629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_2 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (84001975656039 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217384448283 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨2, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (84001975656039 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217384448283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_3 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83967135704397 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217388447659 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨3, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83967135704397 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217388447659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_4 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41966160247039 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217392459503 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨4, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41966160247039 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217392459503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_5 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83897529989223 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217396433729 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨5, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83897529989223 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217396433729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_6 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (10482845519271 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (44348008717 / 2000000000000 : ℝ))
      (E := (cell12988 ⟨6, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (10482845519271 / 12500000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (44348008717 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_7 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83828022953429 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554351118307 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨7, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83828022953429 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554351118307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_8 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41896653175857 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217408494939 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨8, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41896653175857 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217408494939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_9 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83758614313909 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (55435311243 / 2500000000000 : ℝ))
      (E := (cell12988 ⟨9, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83758614313909 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (55435311243 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_10 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83723946805089 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108708230089 / 50000000000000 : ℝ))
      (E := (cell12988 ⟨10, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83723946805089 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108708230089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_11 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83689303790507 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554355118643 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨11, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83689303790507 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554355118643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_12 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83654685235599 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217424498941 / 100000000000000 : ℝ))
      (E := (cell12988 ⟨12, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83654685235599 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (2217424498941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_13 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (41810045552989 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108714240467 / 50000000000000 : ℝ))
      (E := (cell12988 ⟨13, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (41810045552989 / 50000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1108714240467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_14 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83585521367439 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (69294765131 / 3125000000000 : ℝ))
      (E := (cell12988 ⟨14, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83585521367439 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (69294765131 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_15 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (2610967999561 / 3125000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443487302803 / 20000000000000 : ℝ))
      (E := (cell12988 ⟨15, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (2610967999561 / 3125000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (443487302803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_16 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (5219778432979 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (8869762069 / 400000000000 : ℝ))
      (E := (cell12988 ⟨16, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (5219778432979 / 6250000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (8869762069 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_17 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (16696391631779 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554361124661 / 25000000000000 : ℝ))
      (E := (cell12988 ⟨17, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (16696391631779 / 20000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (554361124661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_18 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (83447485646143 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1732381657 / 78125000000 : ℝ))
      (E := (cell12988 ⟨18, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (83447485646143 / 100000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (1732381657 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12988_19 : CellCertificate 12988 (439408023196359 / 5000000000000000 : ℝ) (404301577730079 / 250000000000000000 : ℝ) (326495868776133 / 10000000000000000 : ℝ)
    (cell12988 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · norm_num [cell12988]
  · have h := gap_lower (n := 12988) (a := (20853259339019 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (8869810121 / 400000000000 : ℝ))
      (E := (cell12988 ⟨19, by decide⟩).energy) (xi := (326495868776133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12988 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12988]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12988])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12988) (a := (20853259339019 / 25000000000000 : ℝ)) (b := (158550532599 / 100000000000000 : ℝ)) (q := (8869810121 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12988])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12988]

theorem cert12989_0 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (16814343092771 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277157738691 / 12500000000000 : ℝ))
      (E := (cell12989 ⟨0, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (16814343092771 / 20000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277157738691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_1 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (21009206481917 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108632951477 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨1, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (21009206481917 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108632951477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_2 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (21000490301269 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (5543174731 / 250000000000 : ℝ))
      (E := (cell12989 ⟨2, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (21000490301269 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (5543174731 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_3 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20991780314961 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554318471561 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨3, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20991780314961 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554318471561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_4 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (10491538256991 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217277892603 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨4, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (10491538256991 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217277892603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_5 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (2621797361171 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443456383869 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨5, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (2621797361171 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443456383869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_6 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (10482843716101 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217285916099 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨6, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (10482843716101 / 12500000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217285916099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_7 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83828008534457 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443457989631 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨7, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83828008534457 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443457989631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_8 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41896645969561 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (138580872787 / 6250000000000 : ℝ))
      (E := (cell12989 ⟨8, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41896645969561 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (138580872787 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_9 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83758599907693 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443459582829 / 20000000000000 : ℝ))
      (E := (cell12989 ⟨9, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83758599907693 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (443459582829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_10 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41861966202621 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217301919423 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨10, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41861966202621 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217301919423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_11 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (2615290293657 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554326482171 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨11, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (2615290293657 / 3125000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554326482171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_12 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41827335424237 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108654973983 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨12, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41827335424237 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108654973983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_13 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41810038362603 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217313983061 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨13, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41810038362603 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217313983061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_14 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41792753496507 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554329495337 / 25000000000000 : ℝ))
      (E := (cell12989 ⟨14, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41792753496507 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (554329495337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_15 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20887740404467 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217321948059 / 100000000000000 : ℝ))
      (E := (cell12989 ⟨15, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20887740404467 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (2217321948059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_16 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (20879110141479 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108663002303 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨16, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (20879110141479 / 25000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108663002303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_17 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (41740971901739 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221732998117 / 10000000000000 : ℝ))
      (E := (cell12989 ⟨17, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (41740971901739 / 50000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (221732998117 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_18 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83447471297051 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108666999351 / 50000000000000 : ℝ))
      (E := (cell12989 ⟨18, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83447471297051 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (1108666999351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12989_19 : CellCertificate 12989 (43939464390329 / 500000000000000 : ℝ) (1617081765057979 / 1000000000000000000 : ℝ) (40808768281633 / 1250000000000000 : ℝ)
    (cell12989 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · norm_num [cell12989]
  · have h := gap_lower (n := 12989) (a := (83413023013303 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277167250407 / 12500000000000 : ℝ))
      (E := (cell12989 ⟨19, by decide⟩).energy) (xi := (40808768281633 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12989 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12989]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12989])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12989) (a := (83413023013303 / 100000000000000 : ℝ)) (b := (31707636749 / 20000000000000 : ℝ)) (q := (277167250407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12989])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12989]

theorem cert12990_0 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (42035850501143 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443429483659 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨0, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (42035850501143 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443429483659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_1 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (84036811472519 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217151406119 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨1, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (84036811472519 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217151406119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_2 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (84001946756341 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217155390011 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨2, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (84001946756341 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217155390011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_3 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41983553408759 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443431875669 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨3, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41983553408759 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443431875669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_4 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16786458324001 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277145429647 / 12500000000000 : ℝ))
      (E := (cell12990 ⟨4, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16786458324001 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (277145429647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_5 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16779500225589 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554291850143 / 25000000000000 : ℝ))
      (E := (cell12990 ⟨5, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16779500225589 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (554291850143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_6 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83862735305673 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217171391959 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨6, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83862735305673 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217171391959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_7 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83827994117707 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443435083739 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨7, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83827994117707 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443435083739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_8 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (5237079845547 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217179429859 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨8, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (5237079845547 / 6250000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217179429859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_9 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83758585503697 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108591716117 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨9, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83758585503697 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108591716117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_10 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16744783601523 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443437486471 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨10, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16744783601523 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443437486471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_11 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (261528984393 / 312500000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217191436507 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨11, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (261528984393 / 312500000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217191436507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_12 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83654656463567 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108597725363 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨12, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83654656463567 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108597725363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_13 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83620062346651 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443439896161 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨13, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83620062346651 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443439896161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_14 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (16717098524161 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217203474123 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨14, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (16717098524161 / 20000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217203474123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_15 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (20887736813 / 25000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (22172074941 / 1000000000000 : ℝ))
      (E := (cell12990 ⟨15, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (20887736813 / 25000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (22172074941 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_16 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41758213103191 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (69287858987 / 3125000000000 : ℝ))
      (E := (cell12990 ⟨16, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41758213103191 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (69287858987 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_17 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41740964725137 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108607729659 / 50000000000000 : ℝ))
      (E := (cell12990 ⟨17, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41740964725137 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (1108607729659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_18 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (83447456950171 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217219472067 / 100000000000000 : ℝ))
      (E := (cell12990 ⟨18, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (83447456950171 / 100000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (2217219472067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12990_19 : CellCertificate 12990 (878762533167429 / 10000000000000000 : ℝ) (1616957238377457 / 1000000000000000000 : ℝ) (81611106954607 / 2500000000000000 : ℝ)
    (cell12990 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · norm_num [cell12990]
  · have h := gap_lower (n := 12990) (a := (41706504336371 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443444694377 / 20000000000000 : ℝ))
      (E := (cell12990 ⟨19, by decide⟩).energy) (xi := (81611106954607 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12990 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12990]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12990])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12990) (a := (41706504336371 / 50000000000000 : ℝ)) (b := (19815729603 / 12500000000000 : ℝ)) (q := (443444694377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12990])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12990]

theorem cert12991_0 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (42035843271473 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217032922671 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨0, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (42035843271473 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217032922671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_1 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (42018398509799 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108518452447 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨1, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (42018398509799 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108518452447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_2 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (42000966154917 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554260235279 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨2, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (42000966154917 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554260235279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_3 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41983546188709 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217044923967 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨3, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41983546188709 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217044923967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_4 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41966138593153 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217048919429 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨4, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41966138593153 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217048919429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_5 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83897486700643 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217052935367 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨5, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83897486700643 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217052935367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_6 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83862720884761 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217056921411 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨6, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83862720884761 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217056921411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_7 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83827979703179 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554265235713 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨7, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83827979703179 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554265235713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_8 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83793263120603 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108532474383 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨8, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83793263120603 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108532474383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_9 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83758571101921 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (110853447297 / 5000000000000 : ℝ))
      (E := (cell12991 ⟨9, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83758571101921 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (110853447297 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_10 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83723903612207 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443414588181 / 20000000000000 : ℝ))
      (E := (cell12991 ⟨10, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83723903612207 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (443414588181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_11 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41844630308357 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554269234987 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨11, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41844630308357 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554269234987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_12 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83654642080877 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108540474553 / 50000000000000 : ℝ))
      (E := (cell12991 ⟨12, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83654642080877 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (1108540474553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_13 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (10452505996289 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217084974169 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨13, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (10452505996289 / 12500000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217084974169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_14 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (83585478250811 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217088962519 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨14, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (83585478250811 / 100000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217088962519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_15 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (16710186577669 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277136622197 / 12500000000000 : ℝ))
      (E := (cell12991 ⟨15, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (16710186577669 / 20000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (277136622197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_16 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41758205924531 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217096966183 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨16, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41758205924531 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217096966183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_17 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41740957549641 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (88684039653 / 4000000000000 : ℝ))
      (E := (cell12991 ⟨17, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41740957549641 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (88684039653 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_18 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (41723721302751 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554276249829 / 25000000000000 : ℝ))
      (E := (cell12991 ⟨18, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (41723721302751 / 50000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (554276249829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12991_19 : CellCertificate 12991 (17574715649487 / 200000000000000 : ℝ) (808416365437159 / 500000000000000000 : ℝ) (326418713471189 / 10000000000000000 : ℝ)
    (cell12991 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · norm_num [cell12991]
  · have h := gap_lower (n := 12991) (a := (8341299433439 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217108994423 / 100000000000000 : ℝ))
      (E := (cell12991 ⟨19, by decide⟩).energy) (xi := (326418713471189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12991 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12991]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12991])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12991) (a := (8341299433439 / 10000000000000 : ℝ)) (b := (31702698367 / 20000000000000 : ℝ)) (q := (2217108994423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12991])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12991]

theorem cert12992_0 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16814334417167 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443383684531 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨0, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16814334417167 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443383684531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_1 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16807356513781 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (110846122857 / 5000000000000 : ℝ))
      (E := (cell12992 ⟨1, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16807356513781 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (110846122857 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_2 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (84001917865553 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216926429947 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨2, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (84001917865553 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216926429947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_3 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (10495884742443 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (5542326163 / 250000000000 : ℝ))
      (E := (cell12992 ⟨3, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (10495884742443 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (5542326163 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_4 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (83932262754833 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216934455227 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨4, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (83932262754833 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216934455227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_5 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20974368068891 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138558654111 / 6250000000000 : ℝ))
      (E := (cell12992 ⟨5, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20974368068891 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (138558654111 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_6 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (10482838308259 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216942504457 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨6, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (10482838308259 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216942504457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_7 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41913982645437 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216946462623 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨7, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41913982645437 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216946462623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_8 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (3351729948587 / 4000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (221695046329 / 10000000000000 : ℝ))
      (E := (cell12992 ⟨8, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (3351729948587 / 4000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (221695046329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_9 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41879278351183 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216954513311 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨9, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41879278351183 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216954513311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_10 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41861944609509 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443391700629 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨10, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41861944609509 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443391700629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_11 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16737849245977 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443392499421 / 20000000000000 : ℝ))
      (E := (cell12992 ⟨11, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16737849245977 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (443392499421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_12 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20913656925101 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (88678660049 / 4000000000000 : ℝ))
      (E := (cell12992 ⟨12, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20913656925101 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (88678660049 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_13 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (20905008399047 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108485260649 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨13, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (20905008399047 / 25000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108485260649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_14 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (10448182985379 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216974504703 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨14, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (10448182985379 / 12500000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216974504703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_15 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16710183705381 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108489257431 / 50000000000000 : ℝ))
      (E := (cell12992 ⟨15, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16710183705381 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (1108489257431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_16 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16703279498791 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216982556831 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨16, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16703279498791 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216982556831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_17 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (41740950375251 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216986518957 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨17, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (41740950375251 / 50000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216986518957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_18 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (16689485652609 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (221699052219 / 10000000000000 : ℝ))
      (E := (cell12992 ⟨18, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (16689485652609 / 20000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (221699052219 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12992_19 : CellCertificate 12992 (219677258931607 / 2500000000000000 : ℝ) (808354121272067 / 500000000000000000 : ℝ) (326393003210309 / 10000000000000000 : ℝ)
    (cell12992 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · norm_num [cell12992]
  · have h := gap_lower (n := 12992) (a := (83412979998249 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216994570869 / 100000000000000 : ℝ))
      (E := (cell12992 ⟨19, by decide⟩).energy) (xi := (326393003210309 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12992 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12992]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12992])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12992) (a := (83412979998249 / 100000000000000 : ℝ)) (b := (158501148777 / 100000000000000 : ℝ)) (q := (2216994570869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12992])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12992]

theorem cert12993_0 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (10508957203869 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277100504241 / 12500000000000 : ℝ))
      (E := (cell12993 ⟨0, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (10508957203869 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (277100504241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_1 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (84036768120439 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108404002499 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨1, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (84036768120439 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108404002499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_2 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (42000951711749 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108406015081 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨2, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (42000951711749 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108406015081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_3 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (16793412700779 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2164859377 / 97656250000 : ℝ))
      (E := (cell12993 ⟨3, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (16793412700779 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2164859377 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_4 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83932248325583 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554205011143 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨4, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83932248325583 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554205011143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_5 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83897457852709 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554206012439 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨5, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83897457852709 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554206012439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_6 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (16772538409921 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (110841401257 / 5000000000000 : ℝ))
      (E := (cell12993 ⟨6, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (16772538409921 / 20000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (110841401257 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_7 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83827950880789 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443366407203 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨7, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83827950880789 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443366407203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_8 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (10474154288871 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108418015729 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨8, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (10474154288871 / 12500000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108418015729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_9 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (8375854230503 / 10000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108420038151 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨9, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (8375854230503 / 10000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108420038151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_10 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83723874828047 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108422030503 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨10, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83723874828047 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108422030503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_11 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (3347569273811 / 4000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216848049881 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨11, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (3347569273811 / 4000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216848049881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_12 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (20913653330537 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443370409793 / 20000000000000 : ℝ))
      (E := (cell12993 ⟨12, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (20913653330537 / 25000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (443370409793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_13 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83620019224281 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216856064049 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨13, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83620019224281 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216856064049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_14 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83585449517467 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108430050339 / 50000000000000 : ℝ))
      (E := (cell12993 ⟨14, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83585449517467 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (1108430050339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_15 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41775452083839 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216864105963 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨15, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41775452083839 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216864105963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_16 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (4175819157053 / 5000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216868084893 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨16, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (4175819157053 / 5000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216868084893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_17 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41740943201967 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554218025113 / 25000000000000 : ℝ))
      (E := (cell12993 ⟨17, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41740943201967 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (554218025113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_18 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (83447413922797 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216876098953 / 100000000000000 : ℝ))
      (E := (cell12993 ⟨18, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (83447413922797 / 100000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (2216876098953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12993_19 : CellCertificate 12993 (439341146461373 / 5000000000000000 : ℝ) (64663350935299 / 40000000000000000 : ℝ) (163183648517377 / 5000000000000000 : ℝ)
    (cell12993 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · norm_num [cell12993]
  · have h := gap_lower (n := 12993) (a := (41706482832159 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (69277504467 / 3125000000000 : ℝ))
      (E := (cell12993 ⟨19, by decide⟩).energy) (xi := (163183648517377 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12993 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12993]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12993])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12993) (a := (41706482832159 / 50000000000000 : ℝ)) (b := (158488807649 / 100000000000000 : ℝ)) (q := (69277504467 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12993])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12993]

theorem cert12994_0 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (84071643178297 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554172395743 / 25000000000000 : ℝ))
      (E := (cell12994 ⟨0, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (84071643178297 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554172395743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_1 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (420183768371 / 500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216693606329 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨1, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (420183768371 / 500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216693606329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_2 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (84001888983669 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216697625989 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨2, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (84001888983669 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216697625989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_3 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (8396704907047 / 10000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216701592417 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨3, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (8396704907047 / 10000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216701592417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_4 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41966116949279 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (221670562953 / 10000000000000 : ℝ))
      (E := (cell12994 ⟨4, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41966116949279 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (221670562953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_5 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83897443432077 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (44334192587 / 2000000000000 : ℝ))
      (E := (cell12994 ⟨5, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83897443432077 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (44334192587 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_6 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83862677635359 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108356828699 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨6, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83862677635359 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108356828699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_7 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41913968236463 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (88668706521 / 4000000000000 : ℝ))
      (E := (cell12994 ⟨7, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41913968236463 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (88668706521 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_8 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (2094830497737 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216721653269 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨8, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (2094830497737 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216721653269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_9 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (10469815988739 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216725634911 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨9, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (10469815988739 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216725634911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_10 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (41861930219647 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216729672559 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨10, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (41861930219647 / 50000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216729672559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_11 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83689217462881 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108366828187 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨11, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83689217462881 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108366828187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_12 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83654598946107 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108368825223 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨12, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83654598946107 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108368825223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_13 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (20905001213647 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554185415141 / 25000000000000 : ℝ))
      (E := (cell12994 ⟨13, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (20905001213647 / 25000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (554185415141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_14 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83585435154117 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216745692273 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨14, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83585435154117 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216745692273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_15 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (10443861226333 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216749692687 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨15, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (10443861226333 / 12500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216749692687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_16 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83516368790377 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277094208349 / 12500000000000 : ℝ))
      (E := (cell12994 ⟨16, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83516368790377 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (277094208349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_17 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (83481872059577 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216757677571 / 100000000000000 : ℝ))
      (E := (cell12994 ⟨17, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (83481872059577 / 100000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (2216757677571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_18 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (2086184989619 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1385476081 / 62500000000 : ℝ))
      (E := (cell12994 ⟨18, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (2086184989619 / 2500000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1385476081 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12994_19 : CellCertificate 12994 (87865555406239 / 1000000000000000 : ℝ) (808229661692457 / 500000000000000000 : ℝ) (163170797471743 / 5000000000000000 : ℝ)
    (cell12994 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · norm_num [cell12994]
  · have h := gap_lower (n := 12994) (a := (16682590266519 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108382855323 / 50000000000000 : ℝ))
      (E := (cell12994 ⟨19, by decide⟩).energy) (xi := (163170797471743 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12994 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12994]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12994])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12994) (a := (16682590266519 / 20000000000000 : ℝ)) (b := (158476468453 / 100000000000000 : ℝ)) (q := (1108382855323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12994])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12994]

theorem cert12995_0 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (21017907181967 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216575185469 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨0, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (21017907181967 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216575185469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_1 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (84036739230187 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108289601637 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨1, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (84036739230187 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108289601637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_2 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (42000937273033 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221658321743 / 10000000000000 : ℝ))
      (E := (cell12995 ⟨2, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (42000937273033 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221658321743 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_3 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (8396703463927 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216587236311 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨3, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (8396703463927 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216587236311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_4 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (16786443894751 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443318242021 / 20000000000000 : ℝ))
      (E := (cell12995 ⟨4, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (16786443894751 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443318242021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_5 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41948714506833 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216595262519 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨5, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41948714506833 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216595262519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_6 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (16772532644667 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108299613647 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨6, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (16772532644667 / 20000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108299613647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_7 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41913961033641 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216603227653 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨7, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41913961033641 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216603227653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_8 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (20948301377553 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216607270699 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨8, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (20948301377553 / 25000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216607270699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_9 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83758513517013 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221661124719 / 10000000000000 : ℝ))
      (E := (cell12995 ⟨9, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83758513517013 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (221661124719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_10 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83723846052759 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216615279733 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨10, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83723846052759 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216615279733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_11 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83689203082703 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216619258491 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨11, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83689203082703 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216619258491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_12 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41827292286141 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216623247551 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨12, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41827292286141 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216623247551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_13 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (8361999048711 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108313655423 / 50000000000000 : ℝ))
      (E := (cell12995 ⟨13, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (8361999048711 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (1108313655423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_14 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (4179271039649 / 5000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443326255899 / 20000000000000 : ℝ))
      (E := (cell12995 ⟨14, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (4179271039649 / 5000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (443326255899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_15 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83550875455863 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216635275037 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨15, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83550875455863 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216635275037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_16 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41758177220953 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216639302531 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨16, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41758177220953 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216639302531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_17 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (8348185771743 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554160827139 / 25000000000000 : ℝ))
      (E := (cell12995 ⟨17, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (8348185771743 / 10000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (554160827139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_18 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (83447385248933 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (138540456101 / 6250000000000 : ℝ))
      (E := (cell12995 ⟨18, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (83447385248933 / 100000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (138540456101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12995_19 : CellCertificate 12995 (439314409572223 / 5000000000000000 : ℝ) (1616334892547027 / 1000000000000000000 : ℝ) (326315896935471 / 10000000000000000 : ℝ)
    (cell12995 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · norm_num [cell12995]
  · have h := gap_lower (n := 12995) (a := (41706468501541 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216651332261 / 100000000000000 : ℝ))
      (E := (cell12995 ⟨19, by decide⟩).energy) (xi := (326315896935471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12995 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12995]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12995])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12995) (a := (41706468501541 / 50000000000000 : ℝ)) (b := (79232065593 / 50000000000000 : ℝ)) (q := (2216651332261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12995])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12995]

theorem cert12996_0 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (84071614279667 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216460841417 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨0, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (84071614279667 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216460841417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_1 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (84036724788399 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108232426849 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨1, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (84036724788399 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108232426849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_2 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (42000930055343 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108234431187 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨2, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (42000930055343 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108234431187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_3 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41983510105147 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216472875821 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨3, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41983510105147 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216472875821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_4 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (10491525631397 / 12500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221647684423 / 10000000000000 : ℝ))
      (E := (cell12996 ⟨4, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (10491525631397 / 12500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221647684423 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_5 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41948707298739 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443296178261 / 20000000000000 : ℝ))
      (E := (cell12996 ⟨5, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41948707298739 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443296178261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_6 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (20965662203383 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216484850789 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨6, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (20965662203383 / 25000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216484850789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_7 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83827907663859 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443297780781 / 20000000000000 : ℝ))
      (E := (cell12996 ⟨7, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83827907663859 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (443297780781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_8 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41896595556581 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277061610469 / 12500000000000 : ℝ))
      (E := (cell12996 ⟨8, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41896595556581 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277061610469 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_9 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83758499126331 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108248456571 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨9, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83758499126331 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108248456571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_10 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (2093095791711 / 2500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221650088253 / 10000000000000 : ℝ))
      (E := (cell12996 ⟨10, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (2093095791711 / 2500000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221650088253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_11 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83689188704741 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277063114291 / 12500000000000 : ℝ))
      (E := (cell12996 ⟨11, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83689188704741 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277063114291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_12 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83654570200671 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216508898401 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨12, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83654570200671 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216508898401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_13 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16723995224369 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216512898613 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨13, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16723995224369 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216512898613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_14 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16717081286811 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216516920511 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨14, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16717081286811 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216516920511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_15 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (83550861103273 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108260455603 / 50000000000000 : ℝ))
      (E := (cell12996 ⟨15, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (83550861103273 / 100000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (1108260455603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_16 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (16703268019129 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216524933899 / 100000000000000 : ℝ))
      (E := (cell12996 ⟨16, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (16703268019129 / 20000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (2216524933899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_17 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41740921688747 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221652893517 / 10000000000000 : ℝ))
      (E := (cell12996 ⟨17, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41740921688747 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (221652893517 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_18 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (41723685457657 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277066622223 / 12500000000000 : ℝ))
      (E := (cell12996 ⟨18, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (41723685457657 / 50000000000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (277066622223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12996_19 : CellCertificate 12996 (878602088167999 / 10000000000000000 : ℝ) (1616210480864389 / 1000000000000000000 : ℝ) (163145101504837 / 5000000000000000 : ℝ)
    (cell12996 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · norm_num [cell12996]
  · have h := gap_lower (n := 12996) (a := (1303326916809 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554134237377 / 25000000000000 : ℝ))
      (E := (cell12996 ⟨19, by decide⟩).energy) (xi := (163145101504837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12996 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12996]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12996])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12996) (a := (1303326916809 / 1562500000000 : ℝ)) (b := (19806474481 / 12500000000000 : ℝ)) (q := (554134237377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12996])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12996]

theorem cert12997_0 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (84071599833691 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216346492981 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨0, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (84071599833691 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216346492981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_1 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (84036710348837 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108175249867 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨1, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (84036710348837 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108175249867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_2 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (21000461419383 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216354502931 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨2, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (21000461419383 / 25000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216354502931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_3 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (4198350289177 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554089627737 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨3, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (4198350289177 / 5000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554089627737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_4 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41966095315409 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443272506381 / 20000000000000 : ℝ))
      (E := (cell12997 ⟨4, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41966095315409 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (443272506381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_5 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (8389740018351 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221636651571 / 10000000000000 : ℝ))
      (E := (cell12997 ⟨5, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (8389740018351 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (221636651571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_6 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83862634405949 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108185263941 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨6, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83862634405949 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108185263941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_7 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41913946631327 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138523407361 / 6250000000000 : ℝ))
      (E := (cell12997 ⟨7, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41913946631327 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (138523407361 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_8 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (8379317671833 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554094637613 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨8, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (8379317671833 / 10000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554094637613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_9 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83758484737867 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108191287357 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨9, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83758484737867 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108191287357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_10 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83723817286337 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216386539023 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨10, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83723817286337 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216386539023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_11 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16737834865799 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216390565787 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨11, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16737834865799 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216390565787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_12 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (3346182233251 / 4000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108197272437 / 50000000000000 : ℝ))
      (E := (cell12997 ⟨12, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (3346182233251 / 4000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (1108197272437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_13 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41809980879397 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216398598289 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨13, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41809980879397 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216398598289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_14 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83585392077343 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69262579911 / 3125000000000 : ℝ))
      (E := (cell12997 ⟨14, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83585392077343 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (69262579911 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_15 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16710169350579 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216406601191 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨15, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16710169350579 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216406601191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_16 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (16703265150319 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554102654777 / 25000000000000 : ℝ))
      (E := (cell12997 ⟨16, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (16703265150319 / 20000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (554102654777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_17 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (41740914519883 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (44328292313 / 2000000000000 : ℝ))
      (E := (cell12997 ⟨17, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (41740914519883 / 50000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (44328292313 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_18 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (2607729893247 / 3125000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55410464883 / 2500000000000 : ℝ))
      (E := (cell12997 ⟨18, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (2607729893247 / 3125000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (55410464883 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12997_19 : CellCertificate 12997 (175715072226427 / 2000000000000000 : ℝ) (1616086088332577 / 1000000000000000000 : ℝ) (16313225658253 / 500000000000000 : ℝ)
    (cell12997 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · norm_num [cell12997]
  · have h := gap_lower (n := 12997) (a := (83412908350677 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216422620669 / 100000000000000 : ℝ))
      (E := (cell12997 ⟨19, by decide⟩).energy) (xi := (16313225658253 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12997 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12997]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12997])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12997) (a := (83412908350677 / 100000000000000 : ℝ)) (b := (3960986561 / 2500000000000 : ℝ)) (q := (2216422620669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12997])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12997]

theorem cert12998_0 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (84071585389941 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216232197999 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨0, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (84071585389941 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216232197999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_1 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (84036695911499 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216236199251 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨1, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (84036695911499 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216236199251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_2 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (420009156233 / 500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108120098497 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨2, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (420009156233 / 500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108120098497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_3 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (8396699135901 / 10000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108122099801 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨3, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (8396699135901 / 10000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108122099801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_4 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41966088106341 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2770310269 / 125000000000 : ℝ))
      (E := (cell12998 ⟨4, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41966088106341 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2770310269 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_5 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (20974346442941 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221625219369 / 10000000000000 : ℝ))
      (E := (cell12998 ⟨5, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (20974346442941 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (221625219369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_6 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41931310000293 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554064050149 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨6, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41931310000293 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554064050149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_7 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (20956969715917 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108130121637 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨7, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (20956969715917 / 25000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108130121637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_8 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83793162325717 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108132106387 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨8, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83793162325717 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108132106387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_9 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (4187923517581 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216268231911 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨9, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (4187923517581 / 5000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216268231911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_10 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (1674476058129 / 2000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443254449843 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨10, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (1674476058129 / 2000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443254449843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_11 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83689159955463 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216276270969 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨11, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83689159955463 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216276270969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_12 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83654541464093 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108140122547 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨12, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83654541464093 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108140122547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_13 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (16723989479591 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554071058863 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨13, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (16723989479591 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554071058863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_14 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (83585377722843 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216288247589 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨14, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (83585377722843 / 100000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216288247589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_15 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (10443854050591 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443258457361 / 20000000000000 : ℝ))
      (E := (cell12998 ⟨15, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (10443854050591 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (443258457361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_16 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (16703262281951 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554074074987 / 25000000000000 : ℝ))
      (E := (cell12998 ⟨16, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (16703262281951 / 20000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (554074074987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_17 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (10435226838031 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (27703753647 / 1250000000000 : ℝ))
      (E := (cell12998 ⟨17, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (10435226838031 / 12500000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (27703753647 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_18 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41723671127351 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216304266749 / 100000000000000 : ℝ))
      (E := (cell12998 ⟨18, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41723671127351 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (2216304266749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12998_19 : CellCertificate 12998 (43927431901797 / 500000000000000 : ℝ) (1615961714947169 / 1000000000000000000 : ℝ) (65247765480119 / 2000000000000000 : ℝ)
    (cell12998 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · norm_num [cell12998]
  · have h := gap_lower (n := 12998) (a := (41706447013893 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108154143731 / 50000000000000 : ℝ))
      (E := (cell12998 ⟨19, by decide⟩).energy) (xi := (65247765480119 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12998 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12998]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12998])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12998) (a := (41706447013893 / 50000000000000 : ℝ)) (b := (1980339137 / 1250000000000 : ℝ)) (q := (1108154143731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12998])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12998]

theorem cert12999_0 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (84071570948417 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216117898633 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨0, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (84071570948417 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216117898633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_1 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (42018340738193 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443224378877 / 20000000000000 : ℝ))
      (E := (cell12999 ⟨1, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (42018340738193 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (443224378877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_2 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (21000454204473 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108062943337 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨2, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (21000454204473 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108062943337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_3 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83966976936701 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216129883877 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨3, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83966976936701 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216129883877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_4 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (2622880056149 / 3125000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108066947057 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨4, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (2622880056149 / 3125000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108066947057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_5 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83897371362237 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216137925249 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨5, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83897371362237 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216137925249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_6 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41931302798721 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216141926913 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨6, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41931302798721 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216141926913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_7 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83827864466901 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277018238299 / 12500000000000 : ℝ))
      (E := (cell12999 ⟨7, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83827864466901 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277018238299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_8 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (2094828698383 / 2500000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216149928747 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨8, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (2094828698383 / 2500000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216149928747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_9 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83758455967589 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108076971391 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨9, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83758455967589 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108076971391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_10 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83723788528779 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216157955031 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨10, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83723788528779 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216157955031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_11 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41844572792073 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108080985889 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨11, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41844572792073 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108080985889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_12 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20913631774781 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108082970471 / 50000000000000 : ℝ))
      (E := (cell12999 ⟨12, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20913631774781 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (1108082970471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_13 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83619933039329 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216169984529 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨13, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83619933039329 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216169984529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_14 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (16717072674111 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (110808699591 / 5000000000000 : ℝ))
      (E := (cell12999 ⟨14, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (16717072674111 / 20000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (110808699591 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_15 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83550818058771 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (44323559361 / 2000000000000 : ℝ))
      (E := (cell12999 ⟨15, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83550818058771 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (44323559361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_16 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (20879074267531 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216181976419 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨16, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (20879074267531 / 25000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216181976419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_17 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (41740900185469 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (138511622719 / 6250000000000 : ℝ))
      (E := (cell12999 ⟨17, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (41740900185469 / 50000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (138511622719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_18 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83447327927707 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277023749009 / 12500000000000 : ℝ))
      (E := (cell12999 ⟨18, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83447327927707 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (277023749009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

theorem cert12999_19 : CellCertificate 12999 (1757043837757 / 20000000000000 : ℝ) (323167472140749 / 200000000000000000 : ℝ) (65242629143049 / 2000000000000000 : ℝ)
    (cell12999 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · norm_num [cell12999]
  · have h := gap_lower (n := 12999) (a := (83412879707101 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216194008173 / 100000000000000 : ℝ))
      (E := (cell12999 ⟨19, by decide⟩).energy) (xi := (65242629143049 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12999 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12999]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12999])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12999) (a := (83412879707101 / 100000000000000 : ℝ)) (b := (309403909 / 195312500000 : ℝ)) (q := (2216194008173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12999])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12999]

end BstLean.Part268
