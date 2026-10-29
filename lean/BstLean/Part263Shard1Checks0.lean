import BstLean.Part263Shard1Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12250_0 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (84083049018987 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311368263223 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨0, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (84083049018987 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311368263223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_1 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (1050599074043 / 1250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (462274452693 / 20000000000000 : ℝ))
      (E := (cell12250 ⟨1, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (1050599074043 / 1250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (462274452693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_2 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (84012827972057 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577844056879 / 25000000000000 : ℝ))
      (E := (cell12250 ⟨2, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (84012827972057 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577844056879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_3 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83977755127873 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311380222913 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨3, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83977755127873 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311380222913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_4 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (16788541470823 / 20000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311384201323 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨4, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (16788541470823 / 20000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311384201323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_5 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83907684614207 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311388229811 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨5, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83907684614207 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311388229811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_6 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (41936343435883 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311392201569 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨6, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (41936343435883 / 50000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311392201569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_7 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83837714090599 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577849045781 / 25000000000000 : ℝ))
      (E := (cell12250 ⟨7, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83837714090599 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577849045781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_8 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83802766234707 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288925022861 / 12500000000000 : ℝ))
      (E := (cell12250 ⟨8, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83802766234707 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (288925022861 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_9 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (3350713730731 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (115570210451 / 5000000000000 : ℝ))
      (E := (cell12250 ⟨9, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (3350713730731 / 4000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (115570210451 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_10 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83732945155681 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311408153429 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨10, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83732945155681 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311408153429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_11 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (5231129491343 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311412197683 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨11, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (5231129491343 / 6250000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311412197683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_12 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83663223350443 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155708087561 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨12, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83663223350443 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155708087561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_13 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83628399587479 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311420150819 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨13, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83628399587479 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311420150819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_14 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83593600537713 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311424131597 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨14, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83593600537713 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311424131597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_15 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83558826166443 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577857031009 / 25000000000000 : ℝ))
      (E := (cell12250 ⟨15, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83558826166443 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (577857031009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_16 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83524076439147 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155716067233 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨16, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83524076439147 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155716067233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_17 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (20872337830371 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311436110809 / 100000000000000 : ℝ))
      (E := (cell12250 ⟨17, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (20872337830371 / 25000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (2311436110809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_18 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83454650779291 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155720058509 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨18, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83454650779291 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155720058509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12250_19 : CellCertificate 12250 (35988224234511 / 400000000000000 : ℝ) (1714667950701239 / 1000000000000000000 : ℝ) (346669699379957 / 10000000000000000 : ℝ)
    (cell12250 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · norm_num [cell12250]
  · have h := gap_lower (n := 12250) (a := (83419974778583 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155722050239 / 50000000000000 : ℝ))
      (E := (cell12250 ⟨19, by decide⟩).energy) (xi := (346669699379957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12250 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12250]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12250])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12250) (a := (83419974778583 / 100000000000000 : ℝ)) (b := (16822475233 / 10000000000000 : ℝ)) (q := (1155722050239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12250])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12250]

theorem cert12251_0 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (21020758189387 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311221054051 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨0, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (21020758189387 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311221054051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_1 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (21011977500101 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (231122504839 / 10000000000000 : ℝ))
      (E := (cell12251 ⟨1, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (21011977500101 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (231122504839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_2 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (84012812386943 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311229065149 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨2, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (84012812386943 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311229065149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_3 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83977739880201 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311233056271 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨3, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83977739880201 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311233056271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_4 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (5246418277713 / 6250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311237031203 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨4, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (5246418277713 / 6250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311237031203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_5 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83907670039987 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155620499567 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨5, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83907670039987 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155620499567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_6 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83872672633557 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311245026891 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨6, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83872672633557 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311245026891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_7 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41918850093963 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311249007363 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨7, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41918850093963 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311249007363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_8 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41901376333547 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (57781325171 / 2500000000000 : ℝ))
      (E := (cell12251 ⟨8, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41901376333547 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (57781325171 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_9 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (335071320141 / 400000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311256975507 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨9, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (335071320141 / 400000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311256975507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_10 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20933233064193 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (231126097919 / 10000000000000 : ℝ))
      (E := (cell12251 ⟨10, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20933233064193 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (231126097919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_11 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83698059296223 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (14445406047 / 625000000000 : ℝ))
      (E := (cell12251 ⟨11, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83698059296223 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (14445406047 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_12 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (5228950694897 / 6250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155634473911 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨12, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (5228950694897 / 6250000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155634473911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_13 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83628387688093 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311272927171 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨13, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83628387688093 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311272927171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_14 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20898397242641 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311276912393 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨14, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20898397242641 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311276912393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_15 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83558814931063 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462256182013 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨15, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83558814931063 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462256182013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_16 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (83524065535071 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462256985303 / 20000000000000 : ℝ))
      (E := (cell12251 ⟨16, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (83524065535071 / 100000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (462256985303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_17 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41744670374123 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155644454833 / 50000000000000 : ℝ))
      (E := (cell12251 ⟨17, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41744670374123 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (1155644454833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_18 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (41727320268213 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311292923469 / 100000000000000 : ℝ))
      (E := (cell12251 ⟨18, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (41727320268213 / 50000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (2311292923469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12251_19 : CellCertificate 12251 (224918915939031 / 2500000000000000 : ℝ) (214315992691063 / 125000000000000000 : ℝ) (173320321781477 / 5000000000000000 : ℝ)
    (cell12251 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · norm_num [cell12251]
  · have h := gap_lower (n := 12251) (a := (20854991216407 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577824228827 / 25000000000000 : ℝ))
      (E := (cell12251 ⟨19, by decide⟩).energy) (xi := (173320321781477 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12251 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12251]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12251])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12251) (a := (20854991216407 / 25000000000000 : ℝ)) (b := (168210836769 / 100000000000000 : ℝ)) (q := (577824228827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12251])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12251]

theorem cert12252_0 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (84083016498767 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311073955049 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨0, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (84083016498767 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311073955049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_1 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (84047894079983 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311077943577 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨1, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (84047894079983 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311077943577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_2 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (42006398402201 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577770474379 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨2, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (42006398402201 / 50000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577770474379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_3 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (4198886231753 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155542942203 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨3, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (4198886231753 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155542942203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_4 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83942677535189 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311089913761 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨4, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83942677535189 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311089913761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_5 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20976913867053 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155546939541 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨5, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20976913867053 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155546939541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_6 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (335490633591 / 400000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155548952513 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨6, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (335490633591 / 400000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155548952513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_7 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20959421571903 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155550942241 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨7, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20959421571903 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155550942241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_8 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83802739101799 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311105883739 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨8, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83802739101799 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311105883739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_9 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83767816804501 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (115555492649 / 5000000000000 : ℝ))
      (E := (cell12252 ⟨9, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83767816804501 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (115555492649 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_10 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83732919360097 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311113858031 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨10, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83732919360097 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311113858031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_11 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (1673960934663 / 2000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155558924261 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨11, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (1673960934663 / 2000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155558924261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_12 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83663198888411 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311121831777 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨12, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83663198888411 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311121831777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_13 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (2613386743463 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311125814869 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨13, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (2613386743463 / 3125000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311125814869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_14 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83593577405481 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155564902313 / 50000000000000 : ℝ))
      (E := (cell12252 ⟨14, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83593577405481 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (1155564902313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_15 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20889700924427 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (115556690381 / 5000000000000 : ℝ))
      (E := (cell12252 ⟨15, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20889700924427 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (115556690381 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_16 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83524054632977 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311137772043 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨16, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83524054632977 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311137772043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_17 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (20872332544237 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311141762069 / 100000000000000 : ℝ))
      (E := (cell12252 ⟨17, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (20872332544237 / 25000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (2311141762069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_18 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (4172731514773 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577786445883 / 25000000000000 : ℝ))
      (E := (cell12252 ⟨18, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (4172731514773 / 5000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (577786445883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12252_19 : CellCertificate 12252 (449822863179663 / 5000000000000000 : ℝ) (53574623600577 / 31250000000000000 : ℝ) (173305796370777 / 5000000000000000 : ℝ)
    (cell12252 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · norm_num [cell12252]
  · have h := gap_lower (n := 12252) (a := (83419954954531 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288893722977 / 12500000000000 : ℝ))
      (E := (cell12252 ⟨19, by decide⟩).energy) (xi := (173305796370777 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12252 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12252]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12252])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12252) (a := (83419954954531 / 100000000000000 : ℝ)) (b := (8409846177 / 5000000000000 : ℝ)) (q := (288893722977 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12252])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12252]

theorem cert12253_0 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (84083000242643 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (288865863557 / 12500000000000 : ℝ))
      (E := (cell12253 ⟨0, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (84083000242643 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (288865863557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_1 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (84047878162177 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155465445619 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨1, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (84047878162177 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155465445619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_2 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (84012781224433 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577733724511 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨2, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (84012781224433 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577733724511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_3 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83977709392449 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462187776163 / 20000000000000 : ℝ))
      (E := (cell12253 ⟨3, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83977709392449 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (462187776163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_4 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (5246416414341 / 6250000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310942848997 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨4, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (5246416414341 / 6250000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310942848997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_5 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41953820449441 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310946869653 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨5, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41953820449441 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310946869653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_6 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41936322082173 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577737708993 / 25000000000000 : ℝ))
      (E := (cell12253 ⟨6, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41936322082173 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (577737708993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_7 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83837672389659 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310954814479 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨7, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83837672389659 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310954814479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_8 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41901362769411 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310958813583 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨8, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41901362769411 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310958813583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_9 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20941950894007 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155481420719 / 50000000000000 : ℝ))
      (E := (cell12253 ⟨9, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20941950894007 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (1155481420719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_10 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (41866453232827 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (36108856093 / 1562500000000 : ℝ))
      (E := (cell12253 ⟨10, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (41866453232827 / 50000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (36108856093 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_11 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (20924508543067 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231097078267 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨11, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (20924508543067 / 25000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231097078267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_12 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83663186660619 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (144435923059 / 6250000000000 : ℝ))
      (E := (cell12253 ⟨12, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83663186660619 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (144435923059 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_13 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (16725672779129 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310978755847 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨13, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (16725672779129 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310978755847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_14 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (2612298932577 / 3125000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310982750203 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨14, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (2612298932577 / 3125000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310982750203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_15 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (10444849058297 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310986758587 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨15, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (10444849058297 / 12500000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310986758587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_16 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (16704808746573 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310990729187 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨16, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (16704808746573 / 20000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310990729187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_17 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (8348931960759 / 10000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310994726177 / 100000000000000 : ℝ))
      (E := (cell12253 ⟨17, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (8348931960759 / 10000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (2310994726177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_18 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83454620056393 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231099875539 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨18, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83454620056393 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231099875539 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12253_19 : CellCertificate 12253 (56225987104451 / 625000000000000 : ℝ) (1714247991765521 / 1000000000000000000 : ℝ) (43322818364287 / 1250000000000000 : ℝ)
    (cell12253 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · norm_num [cell12253]
  · have h := gap_lower (n := 12253) (a := (83419945045291 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231100276421 / 10000000000000 : ℝ))
      (E := (cell12253 ⟨19, by decide⟩).energy) (xi := (43322818364287 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12253 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12253]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12253])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12253) (a := (83419945045291 / 100000000000000 : ℝ)) (b := (42045753161 / 25000000000000 : ℝ)) (q := (231100276421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12253])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12253]

theorem cert12254_0 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (84082983989177 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310779914273 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨0, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (84082983989177 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310779914273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_1 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (10505982780873 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155391974583 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨1, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (10505982780873 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155391974583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_2 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16802553129407 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310787951119 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨2, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16802553129407 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310787951119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_3 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41988847076183 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155395964919 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨3, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41988847076183 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155395964919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_4 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (8394264772621 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310795894769 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨4, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (8394264772621 / 10000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310795894769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_5 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (20976906582999 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577699978243 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨5, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (20976906582999 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577699978243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_6 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83872629933343 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577700969409 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨6, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83872629933343 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577700969409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_7 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (5239853655879 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462161571057 / 20000000000000 : ℝ))
      (E := (cell12254 ⟨7, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (5239853655879 / 6250000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (462161571057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_8 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41901355989081 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92432474173 / 4000000000000 : ℝ))
      (E := (cell12254 ⟨8, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41901355989081 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92432474173 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_9 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83767790349829 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (72212996341 / 3125000000000 : ℝ))
      (E := (cell12254 ⟨9, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83767790349829 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (72212996341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_10 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (16746578714689 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310819832951 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨10, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (16746578714689 / 20000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310819832951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_11 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83698021613577 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310823827987 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨11, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83698021613577 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310823827987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_12 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83663174434977 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (231082781737 / 10000000000000 : ℝ))
      (E := (cell12254 ⟨12, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83663174434977 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (231082781737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_13 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83628352002581 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92433272327 / 4000000000000 : ℝ))
      (E := (cell12254 ⟨13, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83628352002581 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (92433272327 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_14 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83593554281511 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310835807221 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨14, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83593554281511 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310835807221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_15 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (20889695309267 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310839821083 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨15, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (20889695309267 / 25000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310839821083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_16 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (41762016417367 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310843797951 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨16, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (41762016417367 / 50000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310843797951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_17 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83489309040173 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155423900997 / 50000000000000 : ℝ))
      (E := (cell12254 ⟨17, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83489309040173 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (1155423900997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_18 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (10431826227403 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310851780863 / 100000000000000 : ℝ))
      (E := (cell12254 ⟨18, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (10431826227403 / 12500000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (2310851780863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12254_19 : CellCertificate 12254 (899585865690631 / 10000000000000000 : ℝ) (428527012791019 / 250000000000000000 : ℝ) (86638376519929 / 2500000000000000 : ℝ)
    (cell12254 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · norm_num [cell12254]
  · have h := gap_lower (n := 12254) (a := (83419935137907 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577713949571 / 25000000000000 : ℝ))
      (E := (cell12254 ⟨19, by decide⟩).energy) (xi := (86638376519929 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12254 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12254]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12254])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12254) (a := (83419935137907 / 100000000000000 : ℝ)) (b := (168169104079 / 100000000000000 : ℝ)) (q := (577713949571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12254])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12254]

theorem cert12255_0 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (42041483869183 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310633088029 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨0, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (42041483869183 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310633088029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_1 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (42023923167203 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310637059573 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨1, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (42023923167203 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310637059573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_2 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (5250796879513 / 6250000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155320528371 / 50000000000000 : ℝ))
      (E := (cell12255 ⟨2, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (5250796879513 / 6250000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (1155320528371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_3 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20994419728703 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310645031477 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨3, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20994419728703 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310645031477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_4 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (1678852656509 / 2000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (57766226277 / 2500000000000 : ℝ))
      (E := (cell12255 ⟨4, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (1678852656509 / 2000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (57766226277 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_5 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83907611767553 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310653009041 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨5, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83907611767553 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310653009041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_6 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41936307852371 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310657030019 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨6, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41936307852371 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310657030019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_7 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83837644600829 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310661006899 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨7, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83837644600829 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310661006899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_8 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83802698419819 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (144416562873 / 6250000000000 : ℝ))
      (E := (cell12255 ⟨8, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83802698419819 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (144416562873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_9 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16753555425181 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310668977403 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨9, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16753555425181 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310668977403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_10 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20933220170867 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310672987031 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨10, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20933220170867 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310672987031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_11 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (20924502264269 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (92427079379 / 4000000000000 : ℝ))
      (E := (cell12255 ⟨11, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (20924502264269 / 25000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (92427079379 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_12 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41831581105741 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310680977059 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨12, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41831581105741 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310680977059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_13 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (10453542513953 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310684971853 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨13, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (10453542513953 / 12500000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310684971853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_14 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83593542722623 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310688975679 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨14, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83593542722623 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310688975679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_15 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41779385004891 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310692936997 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨15, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41779385004891 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310692936997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_16 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (16704804387717 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310696920197 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨16, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (16704804387717 / 20000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310696920197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_17 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (41744649237347 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310700931361 / 100000000000000 : ℝ))
      (E := (cell12255 ⟨17, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (41744649237347 / 50000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (2310700931361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_18 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (83454599583953 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462140983627 / 20000000000000 : ℝ))
      (E := (cell12255 ⟨18, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (83454599583953 / 100000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (462140983627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12255_19 : CellCertificate 12255 (112444492802051 / 1250000000000000 : ℝ) (342793626681707 / 200000000000000000 : ℝ) (173262235118177 / 5000000000000000 : ℝ)
    (cell12255 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · norm_num [cell12255]
  · have h := gap_lower (n := 12255) (a := (4170996261619 / 5000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (288838618031 / 12500000000000 : ℝ))
      (E := (cell12255 ⟨19, by decide⟩).energy) (xi := (173262235118177 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12255 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12255]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12255])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12255) (a := (4170996261619 / 5000000000000 : ℝ)) (b := (42038799461 / 25000000000000 : ℝ)) (q := (288838618031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12255])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12255]

theorem cert12256_0 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (8408295149021 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (11552431571 / 500000000000 : ℝ))
      (E := (cell12256 ⟨0, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (8408295149021 / 10000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (11552431571 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_1 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (2101195760611 / 2500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310490280247 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨1, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (2101195760611 / 2500000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310490280247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_2 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (84012734499951 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310494272723 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨2, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (84012734499951 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310494272723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_3 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (16795532735957 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462099648713 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨3, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (16795532735957 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462099648713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_4 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (3357704717087 / 4000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310502260073 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨4, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (3357704717087 / 4000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310502260073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_5 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83907597205553 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155253136809 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨5, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83907597205553 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155253136809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_6 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (4193630073927 / 5000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310510235221 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨6, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (4193630073927 / 5000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310510235221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_7 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83837630709951 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310514211399 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨7, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83837630709951 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310514211399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_8 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83802684863791 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155259105281 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨8, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83802684863791 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155259105281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_9 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41883881952127 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310522240859 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨9, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41883881952127 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310522240859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_10 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41866433897861 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577631548549 / 25000000000000 : ℝ))
      (E := (cell12256 ⟨10, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41866433897861 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (577631548549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_11 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20924499125691 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462106038823 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨11, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20924499125691 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462106038823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_12 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (16732629998027 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462106837993 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨12, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (16732629998027 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462106837993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_13 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20907082055693 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (144408636801 / 6250000000000 : ℝ))
      (E := (cell12256 ⟨13, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20907082055693 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (144408636801 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_14 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83593531165799 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310542197489 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨14, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83593531165799 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310542197489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_15 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (41779379392259 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155273082221 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨15, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (41779379392259 / 50000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155273082221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_16 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (16704802208883 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155275077033 / 50000000000000 : ℝ))
      (E := (cell12256 ⟨16, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (16704802208883 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (1155275077033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_17 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (16697857582231 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310554172439 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨17, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (16697857582231 / 20000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310554172439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_18 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (83454589350579 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310558167209 / 100000000000000 : ℝ))
      (E := (cell12256 ⟨18, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (83454589350579 / 100000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (2310558167209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12256_19 : CellCertificate 12256 (179905204769477 / 2000000000000000 : ℝ) (1713828238493301 / 1000000000000000000 : ℝ) (346495439382749 / 10000000000000000 : ℝ)
    (cell12256 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · norm_num [cell12256]
  · have h := gap_lower (n := 12256) (a := (20854978832177 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462112428779 / 20000000000000 : ℝ))
      (E := (cell12256 ⟨19, by decide⟩).energy) (xi := (346495439382749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12256 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12256]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12256])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12256) (a := (20854978832177 / 25000000000000 : ℝ)) (b := (8407064697 / 5000000000000 : ℝ)) (q := (462112428779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12256])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12256]

theorem cert12257_0 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (8408293524471 / 10000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310339592787 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨0, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (8408293524471 / 10000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310339592787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_1 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (42023907258543 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288792951399 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨1, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (42023907258543 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288792951399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_2 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (10501589866283 / 12500000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288793449883 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨2, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (10501589866283 / 12500000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288793449883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_3 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16795529689457 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288793945763 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨3, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16795529689457 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288793945763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_4 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16788520606277 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310355579609 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨4, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16788520606277 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310355579609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_5 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16781516529199 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (231035953307 / 10000000000000 : ℝ))
      (E := (cell12257 ⟨5, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16781516529199 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (231035953307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_6 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83872587254739 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288795443893 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨6, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83872587254739 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288795443893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_7 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83837616821431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288795940839 / 12500000000000 : ℝ))
      (E := (cell12257 ⟨7, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83837616821431 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (288795940839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_8 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83802671310079 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310371526059 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨8, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83802671310079 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310371526059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_9 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83767750684877 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155187749681 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨9, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83767750684877 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155187749681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_10 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (327081464493 / 390625000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462075902489 / 20000000000000 : ℝ))
      (E := (cell12257 ⟨10, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (327081464493 / 390625000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462075902489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_11 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41848991975321 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310383514929 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨11, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41848991975321 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310383514929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_12 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (16732627554187 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462077502827 / 20000000000000 : ℝ))
      (E := (cell12257 ⟨12, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (16732627554187 / 20000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (462077502827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_13 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41814158168013 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155195758567 / 50000000000000 : ℝ))
      (E := (cell12257 ⟨13, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41814158168013 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (1155195758567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_14 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41796759805519 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310395472653 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨14, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41796759805519 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310395472653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_15 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (20889686890319 / 25000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310399445307 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨15, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (20889686890319 / 25000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310399445307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_16 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (41762000076113 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310403441421 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨16, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (41762000076113 / 50000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310403441421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_17 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83489277349553 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310407467071 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨17, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83489277349553 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310407467071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_18 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83454579119101 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310411469903 / 100000000000000 : ℝ))
      (E := (cell12257 ⟨18, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83454579119101 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (2310411469903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12257_19 : CellCertificate 12257 (562185068739 / 6250000000000 : ℝ) (342737673282557 / 200000000000000000 : ℝ) (173233206758721 / 5000000000000000 : ℝ)
    (cell12257 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · norm_num [cell12257]
  · have h := gap_lower (n := 12257) (a := (83419905426891 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577603863859 / 25000000000000 : ℝ))
      (E := (cell12257 ⟨19, by decide⟩).energy) (xi := (173233206758721 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12257 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12257]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12257])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12257) (a := (83419905426891 / 100000000000000 : ℝ)) (b := (33625478473 / 20000000000000 : ℝ)) (q := (577603863859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12257])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12257]

theorem cert12258_0 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (84082919001863 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155096490777 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨0, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (84082919001863 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155096490777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_1 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (84047798612343 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310196994623 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨1, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (84047798612343 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310196994623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_2 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16802540672629 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155100488979 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨2, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16802540672629 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155100488979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_3 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83977633217311 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155102470631 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨3, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83977633217311 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155102470631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_4 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41971294069039 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310208951831 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨4, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41971294069039 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310208951831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_5 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (41953784044439 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155106480517 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨5, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (41953784044439 / 50000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155106480517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_6 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (10484071629167 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310216919889 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨6, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (10484071629167 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310216919889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_7 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20959400733817 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310220952839 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨7, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20959400733817 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310220952839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_8 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83802657758681 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310224894511 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨8, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83802657758681 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310224894511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_9 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20941934366943 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310228926833 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨9, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20941934366943 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310228926833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_10 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20933210506731 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155116441891 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨10, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20933210506731 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155116441891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_11 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (20924492850177 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155118444449 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨11, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (20924492850177 / 25000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155118444449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_12 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83663125553881 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288780111441 / 12500000000000 : ℝ))
      (E := (cell12258 ⟨12, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83663125553881 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288780111441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_13 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (10453538056423 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310244898739 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨13, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (10453538056423 / 12500000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310244898739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_14 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (4179675402917 / 5000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310248859261 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨14, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (4179675402917 / 5000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310248859261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_15 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (16711747268011 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310252837707 / 100000000000000 : ℝ))
      (E := (cell12258 ⟨15, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (16711747268011 / 20000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (2310252837707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_16 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (1305062332219 / 1562500000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (5775642101 / 250000000000 : ℝ))
      (E := (cell12258 ⟨16, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (1305062332219 / 1562500000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (5775642101 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_17 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83489266789889 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288782609177 / 12500000000000 : ℝ))
      (E := (cell12258 ⟨17, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83489266789889 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (288782609177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_18 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (1043182111119 / 1250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462052965243 / 20000000000000 : ℝ))
      (E := (cell12258 ⟨18, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (1043182111119 / 1250000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (462052965243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12258_19 : CellCertificate 12258 (89946620082029 / 1000000000000000 : ℝ) (856774258580697 / 500000000000000000 : ℝ) (173218696319487 / 5000000000000000 : ℝ)
    (cell12258 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · norm_num [cell12258]
  · have h := gap_lower (n := 12258) (a := (83419895526929 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155134410331 / 50000000000000 : ℝ))
      (E := (cell12258 ⟨19, by decide⟩).energy) (xi := (173218696319487 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12258 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12258]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12258])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12258) (a := (83419895526929 / 100000000000000 : ℝ)) (b := (262677333 / 156250000000 : ℝ)) (q := (1155134410331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12258])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12258]

theorem cert12259_0 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (8408290276167 / 10000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462009296101 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨0, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (8408290276167 / 10000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462009296101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_1 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (21011945677553 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (115502521527 / 5000000000000 : ℝ))
      (E := (cell12259 ⟨1, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (21011945677553 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (115502521527 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_2 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (16802537559719 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310054467217 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨2, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (16802537559719 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310054467217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_3 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83977617989863 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310058426877 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨3, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83977617989863 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310058426877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_4 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (16788514649451 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310062434599 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨4, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (16788514649451 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310062434599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_5 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83907553534203 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462013288351 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨5, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83907553534203 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462013288351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_6 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (20968139703583 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (3609484999 / 156250000000 : ℝ))
      (E := (cell12259 ⟨6, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (20968139703583 / 25000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (3609484999 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_7 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83837589051461 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310074431857 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨7, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83837589051461 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310074431857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_8 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41901322104799 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231007837387 / 10000000000000 : ℝ))
      (E := (cell12259 ⟨8, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41901322104799 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231007837387 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_9 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83767724252939 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231008240733 / 10000000000000 : ℝ))
      (E := (cell12259 ⟨9, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83767724252939 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (231008240733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_10 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (8373282914587 / 10000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310086366207 / 100000000000000 : ℝ))
      (E := (cell12259 ⟨10, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (8373282914587 / 10000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (2310086366207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_11 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41848979426481 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462018074809 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨11, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41848979426481 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462018074809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_12 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41831556669487 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577523595047 / 25000000000000 : ℝ))
      (E := (cell12259 ⟨12, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41831556669487 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577523595047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_13 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41814146284423 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577524583409 / 25000000000000 : ℝ))
      (E := (cell12259 ⟨13, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41814146284423 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (577524583409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_14 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (10449187063463 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155051178659 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨14, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (10449187063463 / 12500000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155051178659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_15 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41779362560427 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155053170823 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨15, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41779362560427 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155053170823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_16 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (16704795674757 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (72190948469 / 3125000000000 : ℝ))
      (E := (cell12259 ⟨16, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (16704795674757 / 20000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (72190948469 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_17 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83489256232163 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155057166659 / 50000000000000 : ℝ))
      (E := (cell12259 ⟨17, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83489256232163 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (1155057166659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_18 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (41727279330917 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (36095598349 / 1562500000000 : ℝ))
      (E := (cell12259 ⟨18, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (41727279330917 / 50000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (36095598349 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12259_19 : CellCertificate 12259 (179887259271979 / 2000000000000000 : ℝ) (1713408690733541 / 1000000000000000000 : ℝ) (346408376745887 / 10000000000000000 : ℝ)
    (cell12259 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · norm_num [cell12259]
  · have h := gap_lower (n := 12259) (a := (83419885628821 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462024459557 / 20000000000000 : ℝ))
      (E := (cell12259 ⟨19, by decide⟩).energy) (xi := (346408376745887 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12259 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12259]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12259])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12259) (a := (83419885628821 / 100000000000000 : ℝ)) (b := (84049798101 / 50000000000000 : ℝ)) (q := (462024459557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12259])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12259]

theorem cert12260_0 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (8408288652413 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309900031877 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨0, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (8408288652413 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309900031877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_1 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (84047766810691 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309904034519 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨1, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (84047766810691 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309904034519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_2 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (84012672236613 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309908009031 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨2, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (84012672236613 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309908009031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_3 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83977602764941 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154956011473 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨3, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83977602764941 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154956011473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_4 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41971279179457 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309915970059 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨4, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41971279179457 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309915970059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_5 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83907538981967 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (461983995047 / 20000000000000 : ℝ))
      (E := (cell12260 ⟨5, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83907538981967 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (461983995047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_6 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83872544597727 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309923989559 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨6, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83872544597727 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309923989559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_7 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (8383757517001 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309927963767 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨7, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (8383757517001 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309927963767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_8 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20950657665707 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309931964139 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨8, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20950657665707 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309931964139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_9 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83767711040377 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309935940851 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨9, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83767711040377 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309935940851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_10 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (16746563253409 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154969979861 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨10, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (16746563253409 / 20000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154969979861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_11 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83697946307403 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309943912351 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨11, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83697946307403 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309943912351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_12 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83663101126211 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154973961037 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨12, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83663101126211 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154973961037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_13 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83628280688411 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (57748798449 / 2500000000000 : ℝ))
      (E := (cell12260 ⟨13, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83628280688411 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (57748798449 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_14 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (8359348495913 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309955908733 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨14, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (8359348495913 / 10000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309955908733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_15 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (41779356951837 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309959899009 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨15, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (41779356951837 / 50000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309959899009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_16 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (20880991871883 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309963915107 / 100000000000000 : ℝ))
      (E := (cell12260 ⟨16, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (20880991871883 / 25000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (2309963915107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_17 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83489245676373 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115498395247 / 5000000000000 : ℝ))
      (E := (cell12260 ⟨17, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83489245676373 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (115498395247 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_18 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83454548436043 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (461994374853 / 20000000000000 : ℝ))
      (E := (cell12260 ⟨18, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83454548436043 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (461994374853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12260_19 : CellCertificate 12260 (899406396600053 / 10000000000000000 : ℝ) (856634443561819 / 500000000000000000 : ℝ) (346379365836723 / 10000000000000000 : ℝ)
    (cell12260 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · norm_num [cell12260]
  · have h := gap_lower (n := 12260) (a := (83419875732567 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154987943403 / 50000000000000 : ℝ))
      (E := (cell12260 ⟨19, by decide⟩).energy) (xi := (346379365836723 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12260 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12260]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12260])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12260) (a := (83419875732567 / 100000000000000 : ℝ)) (b := (42021425403 / 25000000000000 : ℝ)) (q := (1154987943403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12260])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12260]

theorem cert12261_0 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (42041435144621 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577438423359 / 25000000000000 : ℝ))
      (E := (cell12261 ⟨0, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (42041435144621 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577438423359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_1 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (84047750913779 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309757633203 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨1, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (84047750913779 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309757633203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_2 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (84012656677197 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461952332243 / 20000000000000 : ℝ))
      (E := (cell12261 ⟨2, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (84012656677197 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461952332243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_3 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83977587542543 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309765613809 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨3, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83977587542543 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309765613809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_4 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (2623204483533 / 3125000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154884808033 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨4, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (2623204483533 / 3125000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154884808033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_5 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (20976881108043 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309773619353 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨5, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (20976881108043 / 25000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309773619353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_6 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41936265191759 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461955526517 / 20000000000000 : ℝ))
      (E := (cell12261 ⟨6, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41936265191759 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (461955526517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_7 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41918780645457 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309781606497 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨7, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41918780645457 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309781606497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_8 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83802617118371 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288723200921 / 12500000000000 : ℝ))
      (E := (cell12261 ⟨8, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83802617118371 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (288723200921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_9 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83767697830087 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577447396343 / 25000000000000 : ℝ))
      (E := (cell12261 ⟨9, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83767697830087 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (577447396343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_10 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83732803390449 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230979360633 / 10000000000000 : ℝ))
      (E := (cell12261 ⟨10, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83732803390449 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (230979360633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_11 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (1307780215063 / 1562500000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309797561837 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨11, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (1307780215063 / 1562500000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309797561837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_12 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41831544457797 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309801575231 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨12, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41831544457797 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309801575231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_13 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (522676680063 / 625000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309805537509 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨13, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (522676680063 / 625000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309805537509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_14 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83593473412617 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (5774523929 / 250000000000 : ℝ))
      (E := (cell12261 ⟨14, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83593473412617 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (5774523929 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_15 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (326401182377 / 390625000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154906783957 / 50000000000000 : ℝ))
      (E := (cell12261 ⟨15, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (326401182377 / 390625000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (1154906783957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_16 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83523956603257 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309817532699 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨16, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83523956603257 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309817532699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_17 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83489235122519 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (57745538253 / 2500000000000 : ℝ))
      (E := (cell12261 ⟨17, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83489235122519 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (57745538253 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_18 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (83454538212147 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309825507819 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨18, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (83454538212147 / 100000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309825507819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12261_19 : CellCertificate 12261 (899376501539603 / 10000000000000000 : ℝ) (1713129106326101 / 1000000000000000000 : ℝ) (173175179955013 / 5000000000000000 : ℝ)
    (cell12261 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · norm_num [cell12261]
  · have h := gap_lower (n := 12261) (a := (41709932919083 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309829529519 / 100000000000000 : ℝ))
      (E := (cell12261 ⟨19, by decide⟩).energy) (xi := (173175179955013 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12261 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12261]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12261])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12261) (a := (41709932919083 / 50000000000000 : ℝ)) (b := (168071809349 / 100000000000000 : ℝ)) (q := (2309829529519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12261])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12261]

theorem cert12262_0 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (42041427028503 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309607407421 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨0, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (42041427028503 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309607407421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_1 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (21011933754869 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309611399953 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨1, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (21011933754869 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309611399953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_2 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (21003160280087 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154807682979 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨2, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (21003160280087 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154807682979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_3 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (20994393080667 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154809686483 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨3, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (20994393080667 / 25000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154809686483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_4 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83942528589679 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (18476986981 / 800000000000 : ℝ))
      (E := (cell12262 ⟨4, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83942528589679 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (18476986981 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_5 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (16781501976963 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309627374113 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨5, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (16781501976963 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309627374113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_6 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41936258085853 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (57740783211 / 2500000000000 : ℝ))
      (E := (cell12262 ⟨6, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41936258085853 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (57740783211 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_7 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83837547414173 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309635360049 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨7, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83837547414173 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309635360049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_8 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41901301788113 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309639303559 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨8, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41901301788113 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309639303559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_9 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41883842311033 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154821670449 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨9, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41883842311033 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154821670449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_10 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83732790516081 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154823653017 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨10, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83732790516081 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154823653017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_11 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41848960611423 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577412830627 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨11, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41848960611423 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577412830627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_12 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83663076707121 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144353455101 / 6250000000000 : ℝ))
      (E := (cell12262 ⟨12, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83663076707121 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (144353455101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_13 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83628256933851 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309659306489 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨13, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83628256933851 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309659306489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_14 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (16718692373633 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577415821957 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨14, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (16718692373633 / 20000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577415821957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_15 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (8355869147537 / 10000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309667290247 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨15, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (8355869147537 / 10000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309667290247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_16 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83523945720959 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309671261923 / 100000000000000 : ℝ))
      (E := (cell12262 ⟨16, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83523945720959 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (2309671261923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_17 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (83489224570601 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154837633511 / 50000000000000 : ℝ))
      (E := (cell12262 ⟨17, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (83489224570601 / 100000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (1154837633511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_18 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41727263995073 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461935850637 / 20000000000000 : ℝ))
      (E := (cell12262 ⟨18, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41727263995073 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (461935850637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12262_19 : CellCertificate 12262 (449673305588693 / 5000000000000000 : ℝ) (856494674167673 / 500000000000000000 : ℝ) (346321358964341 / 10000000000000000 : ℝ)
    (cell12262 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · norm_num [cell12262]
  · have h := gap_lower (n := 12262) (a := (41709927972809 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577420806481 / 25000000000000 : ℝ))
      (E := (cell12262 ⟨19, by decide⟩).energy) (xi := (346321358964341 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12262 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12262]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12262])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12262) (a := (41709927972809 / 50000000000000 : ℝ)) (b := (42014479853 / 25000000000000 : ℝ)) (q := (577420806481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12262])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12262]

theorem cert12263_0 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (4204141891371 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577365307899 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨0, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (4204141891371 / 5000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577365307899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_1 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (84047719127781 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309465219197 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨1, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (84047719127781 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309465219197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_2 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (16802525113213 / 20000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (144341823817 / 6250000000000 : ℝ))
      (E := (cell12263 ⟨2, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (16802525113213 / 20000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (144341823817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_3 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83977557105317 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309473184751 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨3, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83977557105317 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309473184751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_4 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83942513708783 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (57736929547 / 2500000000000 : ℝ))
      (E := (cell12263 ⟨4, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83942513708783 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (57736929547 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_5 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83907495339897 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577370295409 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨5, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83907495339897 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577370295409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_6 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83872501962291 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577371283757 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨6, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83872501962291 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577371283757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_7 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41918766769893 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309489166497 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨7, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41918766769893 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309489166497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_8 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41901295018197 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154746584307 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨8, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41901295018197 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154746584307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_9 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (20941917854079 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577374287363 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨9, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (20941917854079 / 25000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577374287363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_10 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83732777643941 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309501116833 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨10, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83732777643941 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309501116833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_11 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41848954341923 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154752568171 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨11, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41848954341923 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154752568171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_12 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (10457883062599 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577377274819 / 25000000000000 : ℝ))
      (E := (cell12263 ⟨12, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (10457883062599 / 12500000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (577377274819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_13 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (3345129802389 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461902625753 / 20000000000000 : ℝ))
      (E := (cell12263 ⟨13, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (3345129802389 / 4000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (461902625753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_14 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83593450325773 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309517115511 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨14, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83593450325773 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309517115511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_15 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83558680264247 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288690133251 / 12500000000000 : ℝ))
      (E := (cell12263 ⟨15, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83558680264247 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (288690133251 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_16 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41761967420319 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154762551391 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨16, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41761967420319 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154762551391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_17 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (83489214020619 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154764528743 / 50000000000000 : ℝ))
      (E := (cell12263 ⟨17, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (83489214020619 / 100000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (1154764528743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_18 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41727258885019 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309533052179 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨18, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41727258885019 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309533052179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12263_19 : CellCertificate 12263 (449658362756121 / 5000000000000000 : ℝ) (1712849613145793 / 1000000000000000000 : ℝ) (346292362998211 / 10000000000000000 : ℝ)
    (cell12263 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · norm_num [cell12263]
  · have h := gap_lower (n := 12263) (a := (41709923027461 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309537034233 / 100000000000000 : ℝ))
      (E := (cell12263 ⟨19, by decide⟩).energy) (xi := (346292362998211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12263 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12263]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12263])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12263) (a := (41709923027461 / 50000000000000 : ℝ)) (b := (168044031801 / 100000000000000 : ℝ)) (q := (2309537034233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12263])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12263]

theorem cert12264_0 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (16816564320097 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309315108199 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨0, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (16816564320097 / 20000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309315108199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_1 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (42023851619347 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154659545469 / 50000000000000 : ℝ))
      (E := (cell12264 ⟨1, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (42023851619347 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1154659545469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_2 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (42006305007173 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1804158677 / 78125000000 : ℝ))
      (E := (cell12264 ⟨2, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (42006305007173 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (1804158677 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_3 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83977541890489 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309327107 / 100000000000 : ℝ))
      (E := (cell12264 ⟨3, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83977541890489 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309327107 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_4 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83942498830367 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309331043833 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨4, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83942498830367 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309331043833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_5 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83907480797417 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309335041923 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨5, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83907480797417 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309335041923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_6 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83872487755271 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309339052351 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨6, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83872487755271 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309339052351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_7 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (10479689958469 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577335756461 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨7, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (10479689958469 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577335756461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_8 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (10475322062359 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577336757171 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨8, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (10475322062359 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577336757171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_9 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41883829106417 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (14433443819 / 625000000000 : ℝ))
      (E := (cell12264 ⟨9, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41883829106417 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (14433443819 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_10 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (20933191193507 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288669379841 / 12500000000000 : ℝ))
      (E := (cell12264 ⟨10, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (20933191193507 / 25000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288669379841 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_11 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (10462237018379 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (115467950167 / 5000000000000 : ℝ))
      (E := (cell12264 ⟨11, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (10462237018379 / 12500000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (115467950167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_12 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41831526148303 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309363028213 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨12, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41831526148303 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309363028213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_13 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83628233187699 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309367004341 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨13, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83628233187699 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309367004341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_14 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (522458992409 / 625000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309370996559 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨14, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (522458992409 / 625000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309370996559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_15 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83558669055141 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288671876429 / 12500000000000 : ℝ))
      (E := (cell12264 ⟨15, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83558669055141 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (288671876429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_16 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (41761961981147 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309378997137 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨16, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (41761961981147 / 50000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309378997137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_17 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83489203472571 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577345739919 / 25000000000000 : ℝ))
      (E := (cell12264 ⟨17, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83489203472571 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (577345739919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_18 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83454507551823 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309386962989 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨18, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83454507551823 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309386962989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12264_19 : CellCertificate 12264 (899286844543011 / 10000000000000000 : ℝ) (1712709900751861 / 1000000000000000000 : ℝ) (346263372010183 / 10000000000000000 : ℝ)
    (cell12264 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · norm_num [cell12264]
  · have h := gap_lower (n := 12264) (a := (83419836166077 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309390954447 / 100000000000000 : ℝ))
      (E := (cell12264 ⟨19, by decide⟩).energy) (xi := (346263372010183 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12264 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12264]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12264])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12264) (a := (83419836166077 / 100000000000000 : ℝ)) (b := (33606029303 / 20000000000000 : ℝ)) (q := (2309390954447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12264])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12264]

theorem cert12265_0 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (420414026881 / 500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461833818999 / 20000000000000 : ℝ))
      (E := (cell12265 ⟨0, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (420414026881 / 500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (461833818999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_1 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (42023843676107 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154586536481 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨1, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (42023843676107 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154586536481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_2 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (10501574308149 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309177084613 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨2, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (10501574308149 / 12500000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309177084613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_3 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83977526678183 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309181081881 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨3, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83977526678183 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309181081881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_4 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (8394248395443 / 10000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309185074199 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨4, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (8394248395443 / 10000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309185074199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_5 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41953733128687 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154594535369 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨5, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41953733128687 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154594535369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_6 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41936236775323 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309193022507 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨6, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41936236775323 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309193022507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_7 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83837505798071 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154598526973 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨7, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83837505798071 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154598526973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_8 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83802562963661 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288650124959 / 12500000000000 : ℝ))
      (E := (cell12265 ⟨8, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83802562963661 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288650124959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_9 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83767645011621 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154602491817 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨9, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83767645011621 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154602491817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_10 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41866375953171 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154604506861 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨10, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41866375953171 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154604506861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_11 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (41848941806201 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309212981527 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨11, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (41848941806201 / 50000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309212981527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_12 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83663040094563 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309217010383 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨12, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83663040094563 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309217010383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_13 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (3345128852711 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577305247821 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨13, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (3345128852711 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577305247821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_14 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83593427247167 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288653123633 / 12500000000000 : ℝ))
      (E := (cell12265 ⟨14, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83593427247167 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (288653123633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_15 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83558657848053 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577307238043 / 25000000000000 : ℝ))
      (E := (cell12265 ⟨15, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83558657848053 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (577307238043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_16 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (3340956523437 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (72163529531 / 3125000000000 : ℝ))
      (E := (cell12265 ⟨16, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (3340956523437 / 4000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (72163529531 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_17 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83489192926457 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154618486797 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨17, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83489192926457 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154618486797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_18 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (83454497335501 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309240927429 / 100000000000000 : ℝ))
      (E := (cell12265 ⟨18, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (83454497335501 / 100000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (2309240927429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12265_19 : CellCertificate 12265 (449628484134267 / 5000000000000000 : ℝ) (1712570211147973 / 1000000000000000000 : ℝ) (346234385998803 / 10000000000000000 : ℝ)
    (cell12265 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · norm_num [cell12265]
  · have h := gap_lower (n := 12265) (a := (20854956569771 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154622464179 / 50000000000000 : ℝ))
      (E := (cell12265 ⟨19, by decide⟩).energy) (xi := (346234385998803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12265 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12265]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12265])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12265) (a := (20854956569771 / 25000000000000 : ℝ)) (b := (84008131777 / 50000000000000 : ℝ)) (q := (1154622464179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12265])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12265]

theorem cert12266_0 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (84082789154563 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (92360925369 / 4000000000000 : ℝ))
      (E := (cell12266 ⟨0, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (84082789154563 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (92360925369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_1 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (84047671468341 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288628395659 / 12500000000000 : ℝ))
      (E := (cell12266 ⟨1, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (84047671468341 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288628395659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_2 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (42006289459301 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309031115233 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨2, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (42006289459301 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309031115233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_3 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41988755734199 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577258777349 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨3, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41988755734199 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577258777349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_4 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83942469080973 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144314943713 / 6250000000000 : ℝ))
      (E := (cell12266 ⟨4, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83942469080973 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (144314943713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_5 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (10488431464971 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309043094439 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨5, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (10488431464971 / 12500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309043094439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_6 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (1310507177319 / 1562500000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154523551701 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨6, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (1310507177319 / 1562500000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154523551701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_7 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41918745965371 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154525538511 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨7, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41918745965371 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154525538511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_8 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (2095063735769 / 2500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309055081579 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨8, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (2095063735769 / 2500000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309055081579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_9 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20941907953169 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309059067239 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨9, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20941907953169 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309059067239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_10 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41866369520441 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154531520909 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨10, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41866369520441 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154531520909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_11 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (20924467769989 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309067070903 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨11, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (20924467769989 / 25000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309067070903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_12 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41831513947331 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577267761447 / 25000000000000 : ℝ))
      (E := (cell12266 ⟨12, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41831513947331 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (577267761447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_13 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83628209449951 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288634378941 / 12500000000000 : ℝ))
      (E := (cell12266 ⟨13, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83628209449951 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288634378941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_14 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83593415710953 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309079034937 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨14, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83593415710953 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309079034937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_15 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83558646642981 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154541502231 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨15, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83558646642981 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154541502231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_16 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83523902211531 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154543502243 / 50000000000000 : ℝ))
      (E := (cell12266 ⟨16, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83523902211531 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (1154543502243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_17 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83489182382277 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309091041077 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨17, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83489182382277 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309091041077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_18 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (83454487121071 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288636875461 / 12500000000000 : ℝ))
      (E := (cell12266 ⟨18, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (83454487121071 / 100000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (288636875461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12266_19 : CellCertificate 12266 (224806774171913 / 2500000000000000 : ℝ) (856215272164277 / 500000000000000000 : ℝ) (346205404962619 / 10000000000000000 : ℝ)
    (cell12266 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · norm_num [cell12266]
  · have h := gap_lower (n := 12266) (a := (41709908196971 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309099014177 / 100000000000000 : ℝ))
      (E := (cell12266 ⟨19, by decide⟩).energy) (xi := (346205404962619 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12266 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12266]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12266])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12266) (a := (41709908196971 / 50000000000000 : ℝ)) (b := (168002382917 / 100000000000000 : ℝ)) (q := (2309099014177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12266])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12266]

theorem cert12267_0 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (42041386467787 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154438641827 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨0, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (42041386467787 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154438641827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_1 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (84047655587073 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154440655043 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨1, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (84047655587073 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154440655043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_2 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (3360502534983 / 4000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288610657029 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨2, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (3360502534983 / 4000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288610657029 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_3 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83977496261133 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154444623691 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨3, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83977496261133 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154444623691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_4 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41971227104997 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154446617589 / 50000000000000 : ℝ))
      (E := (cell12267 ⟨4, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41971227104997 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (1154446617589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_5 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41953718592299 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288612153599 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨5, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41953718592299 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288612153599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_6 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83872445148579 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461780247427 / 20000000000000 : ℝ))
      (E := (cell12267 ⟨6, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83872445148579 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461780247427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_7 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20959369516441 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308905210931 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨7, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20959369516441 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308905210931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_8 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83802535900169 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308909216457 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨8, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83802535900169 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308909216457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_9 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83767618615999 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308913203881 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨9, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83767618615999 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308913203881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_10 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83732726177647 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288614654877 / 12500000000000 : ℝ))
      (E := (cell12267 ⟨10, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83732726177647 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (288614654877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_11 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83697858549693 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577230303363 / 25000000000000 : ℝ))
      (E := (cell12267 ⟨11, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83697858549693 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (577230303363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_12 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83663015696903 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (92357007699 / 4000000000000 : ℝ))
      (E := (cell12267 ⟨12, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83663015696903 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (92357007699 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_13 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83628197584227 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461785836629 / 20000000000000 : ℝ))
      (E := (cell12267 ⟨13, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83628197584227 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (461785836629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_14 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20898351044199 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308933192273 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨14, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20898351044199 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308933192273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_15 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (41779317719963 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144308573019 / 6250000000000 : ℝ))
      (E := (cell12267 ⟨15, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (41779317719963 / 50000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144308573019 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_16 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (83523891339113 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308941175621 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨16, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (83523891339113 / 100000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308941175621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_17 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (8348917184003 / 10000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308945162131 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨17, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (8348917184003 / 10000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308945162131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_18 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (20863619227133 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144309320849 / 6250000000000 : ℝ))
      (E := (cell12267 ⟨18, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (20863619227133 / 25000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (144309320849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12267_19 : CellCertificate 12267 (112399653724901 / 1250000000000000 : ℝ) (1712290900288029 / 1000000000000000000 : ℝ) (346176428900179 / 10000000000000000 : ℝ)
    (cell12267 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · norm_num [cell12267]
  · have h := gap_lower (n := 12267) (a := (1668396130213 / 2000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308953153697 / 100000000000000 : ℝ))
      (E := (cell12267 ⟨19, by decide⟩).energy) (xi := (346176428900179 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12267 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12267]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12267])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12267) (a := (1668396130213 / 2000000000000 : ℝ)) (b := (83994252301 / 50000000000000 : ℝ)) (q := (2308953153697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12267])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12267]

theorem cert12268_0 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (42041378359617 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308731543279 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨0, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (42041378359617 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308731543279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_1 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (8404763970841 / 10000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308735507401 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨1, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (8404763970841 / 10000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308735507401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_2 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (84012547833111 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308739507611 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨2, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (84012547833111 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308739507611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_3 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83977481056389 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308743495837 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨3, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83977481056389 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308743495837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_4 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20985609835373 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230874748151 / 10000000000000 : ℝ))
      (E := (cell12268 ⟨4, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20985609835373 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230874748151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_5 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83907422651863 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577187868449 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨5, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83907422651863 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577187868449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_6 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (2621013467223 / 3125000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308755481609 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨6, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (2621013467223 / 3125000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308755481609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_7 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41918732101569 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230875945567 / 10000000000000 : ℝ))
      (E := (cell12268 ⟨7, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41918732101569 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230875945567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_8 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83802522371887 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308763462257 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨8, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83802522371887 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308763462257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_9 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20941901355397 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461753490307 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨9, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20941901355397 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461753490307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_10 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83732713316637 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308771431319 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨10, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83732713316637 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308771431319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_11 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41848923010807 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230877540917 / 10000000000000 : ℝ))
      (E := (cell12268 ⟨11, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41848923010807 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (230877540917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_12 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (16732600700257 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461755890089 / 20000000000000 : ℝ))
      (E := (cell12268 ⟨12, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (16732600700257 / 20000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (461755890089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_13 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41814092860301 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154391723067 / 50000000000000 : ℝ))
      (E := (cell12268 ⟨13, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41814092860301 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (1154391723067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_14 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83593392644697 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308787402979 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨14, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83593392644697 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308787402979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_15 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (83558624238887 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308791385583 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨15, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (83558624238887 / 100000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308791385583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_16 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20880970117167 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (115439770013 / 5000000000000 : ℝ))
      (E := (cell12268 ⟨16, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20880970117167 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (115439770013 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_17 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (20872290324929 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577199848729 / 25000000000000 : ℝ))
      (E := (cell12268 ⟨17, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (20872290324929 / 25000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (577199848729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_18 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (41727233348943 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308803375299 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨18, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (41727233348943 / 50000000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308803375299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12268_19 : CellCertificate 12268 (899167367602043 / 10000000000000000 : ℝ) (68486051160833 / 40000000000000000 : ℝ) (346147457810031 / 10000000000000000 : ℝ)
    (cell12268 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · norm_num [cell12268]
  · have h := gap_lower (n := 12268) (a := (10427474578651 / 12500000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308807346919 / 100000000000000 : ℝ))
      (E := (cell12268 ⟨19, by decide⟩).energy) (xi := (346147457810031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12268 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12268]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12268])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12268) (a := (10427474578651 / 12500000000000 : ℝ)) (b := (167974628611 / 100000000000000 : ℝ)) (q := (2308807346919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12268])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12268]

theorem cert12269_0 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (4204137025277 / 5000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (144286615959 / 6250000000000 : ℝ))
      (E := (cell12269 ⟨0, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (4204137025277 / 5000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (144286615959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_1 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (2626488244761 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308589815009 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨1, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (2626488244761 / 3125000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308589815009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_2 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (84012532294209 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308593811563 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨2, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (84012532294209 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308593811563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_3 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16795493170833 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308597796933 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨3, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16795493170833 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308597796933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_4 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (20985606118867 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577150445137 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨4, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (20985606118867 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577150445137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_5 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83907408121563 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (92344230863 / 4000000000000 : ℝ))
      (E := (cell12269 ⟨5, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83907408121563 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (92344230863 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_6 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16774483351217 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577152444731 / 25000000000000 : ℝ))
      (E := (cell12269 ⟨6, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16774483351217 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (577152444731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_7 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41918725171431 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154306876659 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨7, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41918725171431 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154306876659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_8 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (10475313605739 / 12500000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308617761033 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨8, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (10475313605739 / 12500000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308617761033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_9 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (20941898057361 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308621752231 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨9, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (20941898057361 / 25000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308621752231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_10 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83732700457851 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288578216841 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨10, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83732700457851 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288578216841 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_11 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83697833495717 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308629774107 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨11, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83697833495717 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308629774107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_12 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83662991307807 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288579220207 / 12500000000000 : ℝ))
      (E := (cell12269 ⟨12, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83662991307807 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (288579220207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_13 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (3345126954363 / 4000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308637704363 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨13, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (3345126954363 / 4000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308637704363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_14 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16718676222931 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (46172834503 / 2000000000000 : ℝ))
      (E := (cell12269 ⟨14, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16718676222931 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (46172834503 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_15 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83558613039863 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308645714417 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨15, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83558613039863 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308645714417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_16 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41761934800099 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (72145304267 / 3125000000000 : ℝ))
      (E := (cell12269 ⟨16, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41761934800099 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (72145304267 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_17 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (41744575380667 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308653681273 / 100000000000000 : ℝ))
      (E := (cell12269 ⟨17, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (41744575380667 / 50000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (2308653681273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_18 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (83454456489129 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154328835327 / 50000000000000 : ℝ))
      (E := (cell12269 ⟨18, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (83454456489129 / 100000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (1154328835327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12269_19 : CellCertificate 12269 (899137510094999 / 10000000000000000 : ℝ) (1712011680521373 / 1000000000000000000 : ℝ) (173059245845363 / 5000000000000000 : ℝ)
    (cell12269 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · norm_num [cell12269]
  · have h := gap_lower (n := 12269) (a := (16683957349923 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461732342053 / 20000000000000 : ℝ))
      (E := (cell12269 ⟨19, by decide⟩).energy) (xi := (173059245845363 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12269 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12269]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12269])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12269) (a := (16683957349923 / 20000000000000 : ℝ)) (b := (167960754941 / 100000000000000 : ℝ)) (q := (461732342053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12269])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12269]

theorem cert12270_0 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (21020681073623 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308440219849 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨0, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (21020681073623 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308440219849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_1 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (84047607958897 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308444232911 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨1, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (84047607958897 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308444232911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_2 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (21003129189467 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308448225899 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨2, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (21003129189467 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308448225899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_3 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83977450654459 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308452208503 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨3, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83977450654459 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308452208503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_4 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83942409611921 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (46169123803 / 2000000000000 : ℝ))
      (E := (cell12270 ⟨4, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83942409611921 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (46169123803 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_5 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83907393593697 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308460180009 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨5, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83907393593697 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308460180009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_6 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41936201281713 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461692837397 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨6, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41936201281713 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461692837397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_7 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (10479679560617 / 12500000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308468161801 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨7, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (10479679560617 / 12500000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308468161801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_8 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (41901247661123 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308472170733 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨8, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (41901247661123 / 50000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308472170733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_9 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (16753515807913 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308476163943 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨9, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (16753515807913 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308476163943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_10 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83732687601289 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577120037311 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨10, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83732687601289 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577120037311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_11 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83697820972001 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308484134197 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨11, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83697820972001 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308484134197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_12 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (8366297911647 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577122031527 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨12, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (8366297911647 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577122031527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_13 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83628161999647 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577123033009 / 25000000000000 : ℝ))
      (E := (cell12270 ⟨13, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83628161999647 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (577123033009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_14 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (8359336958667 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461699220139 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨14, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (8359336958667 / 10000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461699220139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_15 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (16711720368571 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308500096691 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨15, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (16711720368571 / 20000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308500096691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_16 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (835238587337 / 1000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461700825267 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨16, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (835238587337 / 1000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461700825267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_17 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (20872285056221 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461701615873 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨17, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (20872285056221 / 25000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461701615873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_18 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83454446282263 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308512077833 / 100000000000000 : ℝ))
      (E := (cell12270 ⟨18, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83454446282263 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (2308512077833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12270_19 : CellCertificate 12270 (22477691431923 / 250000000000000 : ℝ) (342374420956821 / 200000000000000000 : ℝ) (86522382635203 / 2500000000000000 : ℝ)
    (cell12270 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · norm_num [cell12270]
  · have h := gap_lower (n := 12270) (a := (83419776871871 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461703213821 / 20000000000000 : ℝ))
      (E := (cell12270 ⟨19, by decide⟩).energy) (xi := (86522382635203 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12270 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12270]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12270])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12270) (a := (83419776871871 / 100000000000000 : ℝ)) (b := (167946883593 / 100000000000000 : ℝ)) (q := (461703213821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12270])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12270]

theorem cert12271_0 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (84082708086091 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154147347279 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨0, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (84082708086091 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154147347279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_1 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (42023796044023 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308298703321 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨1, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (42023796044023 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308298703321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_2 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (10501562653011 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308302692811 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨2, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (10501562653011 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308302692811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_3 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (10497179432159 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577076668179 / 25000000000000 : ℝ))
      (E := (cell12271 ⟨3, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (10497179432159 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577076668179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_4 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83942394750849 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (144269415779 / 6250000000000 : ℝ))
      (E := (cell12271 ⟨4, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83942394750849 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (144269415779 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_5 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (16781475813653 / 20000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308314641219 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨5, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (16781475813653 / 20000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308314641219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_6 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83872388373159 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308318647889 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨6, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83872388373159 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308318647889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_7 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83837422629359 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577080655799 / 25000000000000 : ℝ))
      (E := (cell12271 ⟨7, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83837422629359 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577080655799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_8 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83802481800887 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577081658353 / 25000000000000 : ℝ))
      (E := (cell12271 ⟨8, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83802481800887 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (577081658353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_9 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (5235472865747 / 6250000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308330628699 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨9, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (5235472865747 / 6250000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308330628699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_10 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (1674653494939 / 2000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308334616871 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨10, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (1674653494939 / 2000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308334616871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_11 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83697808450467 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461667721097 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨11, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83697808450467 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461667721097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_12 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (10457870865909 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308342601849 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨12, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (10457870865909 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308342601849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_13 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83628150142317 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (115417330651 / 5000000000000 : ℝ))
      (E := (cell12271 ⟨13, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83628150142317 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (115417330651 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_14 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (4179667903037 / 5000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308350587711 / 100000000000000 : ℝ))
      (E := (cell12271 ⟨14, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (4179667903037 / 5000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (2308350587711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_15 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (4177929532393 / 5000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (92334183621 / 4000000000000 : ℝ))
      (E := (cell12271 ⟨15, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (4177929532393 / 5000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (92334183621 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_16 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (10440480983647 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154179284817 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨16, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (10440480983647 / 12500000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154179284817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_17 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (41744564845183 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461672517839 / 20000000000000 : ℝ))
      (E := (cell12271 ⟨17, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (41744564845183 / 50000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (461672517839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_18 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (83454436077287 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154183269327 / 50000000000000 : ℝ))
      (E := (cell12271 ⟨18, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (83454436077287 / 100000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (1154183269327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12271_19 : CellCertificate 12271 (899077809146649 / 10000000000000000 : ℝ) (427933137950863 / 250000000000000000 : ℝ) (173030287179421 / 5000000000000000 : ℝ)
    (cell12271 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · norm_num [cell12271]
  · have h := gap_lower (n := 12271) (a := (3336790679839 / 4000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288546317483 / 12500000000000 : ℝ))
      (E := (cell12271 ⟨19, by decide⟩).energy) (xi := (173030287179421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12271 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12271]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12271])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12271) (a := (3336790679839 / 4000000000000 : ℝ)) (b := (33586602913 / 20000000000000 : ℝ)) (q := (288546317483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12271])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12271]

theorem cert12272_0 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (42041345940167 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154074639737 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨0, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (42041345940167 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154074639737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_1 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (84047576219797 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577038321007 / 25000000000000 : ℝ))
      (E := (cell12272 ⟨1, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (84047576219797 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (577038321007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_2 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (84012485692867 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308157270111 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨2, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (84012485692867 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308157270111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_3 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41988710131301 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (144260077963 / 6250000000000 : ℝ))
      (E := (cell12272 ⟨3, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41988710131301 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (144260077963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_4 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83942379892253 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461633045069 / 20000000000000 : ℝ))
      (E := (cell12272 ⟨4, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83942379892253 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (461633045069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_5 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41953682272633 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308169213089 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨5, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41953682272633 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308169213089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_6 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41936187092641 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288521652443 / 12500000000000 : ℝ))
      (E := (cell12272 ⟨6, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41936187092641 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288521652443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_7 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83837408776131 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230817719543 / 10000000000000 : ℝ))
      (E := (cell12272 ⟨7, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83837408776131 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (230817719543 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_8 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (16760493656367 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (115409060351 / 5000000000000 : ℝ))
      (E := (cell12272 ⟨8, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (16760493656367 / 20000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (115409060351 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_9 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83767552666603 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (92327408179 / 4000000000000 : ℝ))
      (E := (cell12272 ⟨9, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83767552666603 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (92327408179 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_10 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41866330947417 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288523649451 / 12500000000000 : ℝ))
      (E := (cell12272 ⟨10, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41866330947417 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (288523649451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_11 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41848897965557 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308193187973 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨11, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41848897965557 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308193187973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_12 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20915738685053 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (28852464861 / 1250000000000 : ℝ))
      (E := (cell12272 ⟨12, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20915738685053 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (28852464861 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_13 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (20907034571771 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308201147313 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨13, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (20907034571771 / 25000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308201147313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_14 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (41796673268433 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154102564051 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨14, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (41796673268433 / 50000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154102564051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_15 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83558579454879 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154104568901 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨15, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83558579454879 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154104568901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_16 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83523837006623 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308213124583 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨16, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83523837006623 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308213124583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_17 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (83489119157777 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154108576301 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨17, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (83489119157777 / 100000000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154108576301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_18 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (417272129371 / 500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308221111303 / 100000000000000 : ℝ))
      (E := (cell12272 ⟨18, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (417272129371 / 500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (2308221111303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12272_19 : CellCertificate 12272 (899047965703029 / 10000000000000000 : ℝ) (34231860431477 / 20000000000000000 : ℝ) (346031623143367 / 10000000000000000 : ℝ)
    (cell12272 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · norm_num [cell12272]
  · have h := gap_lower (n := 12272) (a := (10427469640241 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154112561269 / 50000000000000 : ℝ))
      (E := (cell12272 ⟨19, by decide⟩).energy) (xi := (346031623143367 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12272 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12272]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12272])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12272) (a := (10427469640241 / 12500000000000 : ℝ)) (b := (83959573929 / 50000000000000 : ℝ)) (q := (1154112561269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12272])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12272]

theorem cert12273_0 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (42041337838611 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154001958417 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨0, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (42041337838611 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154001958417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_1 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (1680951207083 / 2000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (36062623707 / 1562500000000 : ℝ))
      (E := (cell12273 ⟨1, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (1680951207083 / 2000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (36062623707 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_2 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (42006235082103 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230801189999 / 10000000000000 : ℝ))
      (E := (cell12273 ⟨2, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (42006235082103 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (230801189999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_3 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83977405070449 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154007937373 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨3, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83977405070449 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154007937373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_4 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83942365036131 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308019850941 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨4, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83942365036131 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308019850941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_5 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (839073500247 / 1000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (115401194781 / 5000000000000 : ℝ))
      (E := (cell12273 ⟨5, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (839073500247 / 1000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (115401194781 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_6 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20968089999949 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577006961011 / 25000000000000 : ℝ))
      (E := (cell12273 ⟨6, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20968089999949 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (577006961011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_7 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83837394925251 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154015939253 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨7, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83837394925251 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154015939253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_8 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (2618826711409 / 3125000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308035833609 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨8, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (2618826711409 / 3125000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308035833609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_9 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41883769741759 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308039833299 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨9, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41883769741759 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308039833299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_10 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (4186632452247 / 5000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154021913729 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨10, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (4186632452247 / 5000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154021913729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_11 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83697783413941 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154023911821 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨11, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83697783413941 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154023911821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_12 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (20915735638823 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154025914579 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨12, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (20915735638823 / 25000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154025914579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_13 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83628126433947 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308055792991 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨13, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83628126433947 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308055792991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_14 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83593335015047 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154029889983 / 50000000000000 : ℝ))
      (E := (cell12273 ⟨14, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83593335015047 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (1154029889983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_15 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (10444821032989 / 12500000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (14425398729 / 625000000000 : ℝ))
      (E := (cell12273 ⟨15, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (10444821032989 / 12500000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (14425398729 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_16 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41761913073021 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308067791183 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨16, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41761913073021 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308067791183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_17 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (1043613857839 / 1250000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461614353917 / 20000000000000 : ℝ))
      (E := (cell12273 ⟨17, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (1043613857839 / 1250000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (461614353917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_18 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (41727207836501 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308075795783 / 100000000000000 : ℝ))
      (E := (cell12273 ⟨18, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (41727207836501 / 50000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (2308075795783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12273_19 : CellCertificate 12273 (179803625388981 / 2000000000000000 : ℝ) (1711453514089737 / 1000000000000000000 : ℝ) (17300133844647 / 500000000000000 : ℝ)
    (cell12273 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · norm_num [cell12273]
  · have h := gap_lower (n := 12273) (a := (83419747249727 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (92323190357 / 4000000000000 : ℝ))
      (E := (cell12273 ⟨19, by decide⟩).energy) (xi := (17300133844647 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12273 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12273]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12273])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12273) (a := (83419747249727 / 100000000000000 : ℝ)) (b := (16790528347 / 10000000000000 : ℝ)) (q := (92323190357 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12273])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12273]

theorem cert12274_0 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (84082659476753 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307858606643 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨0, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (84082659476753 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307858606643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_1 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (2626485765347 / 3125000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153931301491 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨1, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (2626485765347 / 3125000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153931301491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_2 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (10501556829763 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153933320131 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨2, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (10501556829763 / 12500000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153933320131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_3 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83977389880813 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153935306283 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨3, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83977389880813 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153935306283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_4 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83942350182483 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (230787458711 / 10000000000000 : ℝ))
      (E := (cell12274 ⟨4, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83942350182483 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (230787458711 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_5 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (16781467101313 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576969643263 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨5, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (16781467101313 / 20000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576969643263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_6 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83872345816699 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (23078825793 / 1000000000000 : ℝ))
      (E := (cell12274 ⟨6, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83872345816699 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (23078825793 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_7 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83837381076719 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307886556569 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨7, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83837381076719 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307886556569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_8 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83802441250647 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576972642783 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨8, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83802441250647 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576972642783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_9 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83767526302697 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307894573147 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨9, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83767526302697 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307894573147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_10 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20933159049317 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307898570423 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨10, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20933159049317 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307898570423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_11 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (20924442724737 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576975642629 / 25000000000000 : ℝ))
      (E := (cell12274 ⟨11, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (20924442724737 / 25000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (576975642629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_12 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83662930372509 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461581304537 / 20000000000000 : ℝ))
      (E := (cell12274 ⟨12, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83662930372509 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (461581304537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_13 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83628114582907 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307910550051 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨13, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83628114582907 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307910550051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_14 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83593323495283 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307914543303 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨14, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83593323495283 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307914543303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_15 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83558557074957 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307918508927 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨15, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83558557074957 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307918508927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_16 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83523815287433 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307922511297 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨16, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83523815287433 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307922511297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_17 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83489098098391 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153963249157 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨17, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83489098098391 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153963249157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_18 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (83454405473693 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153965237861 / 50000000000000 : ℝ))
      (E := (cell12274 ⟨18, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (83454405473693 / 100000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (1153965237861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

theorem cert12274_19 : CellCertificate 12274 (898988292871121 / 10000000000000000 : ℝ) (1711314029345551 / 1000000000000000000 : ℝ) (69194747121223 / 2000000000000000 : ℝ)
    (cell12274 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · norm_num [cell12274]
  · have h := gap_lower (n := 12274) (a := (41709868689687 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307934507233 / 100000000000000 : ℝ))
      (E := (cell12274 ⟨19, by decide⟩).energy) (xi := (69194747121223 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12274 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12274]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12274])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12274) (a := (41709868689687 / 50000000000000 : ℝ)) (b := (839457107 / 500000000000 : ℝ)) (q := (2307934507233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12274])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12274]

end BstLean.Part263
